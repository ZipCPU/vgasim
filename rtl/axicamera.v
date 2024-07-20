////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/axicamera.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Controls video ingest to memory from some form of video source,
//		either a "camera" or something else.
//
// Registers:
//	Addr(hex) Register at that address (RO = read only)
//	------	-----------------------------
//	000:	(DMA) Control, color mapping, lock status
//
//	004:	DMA line words		(Must match to stay in sync)
//	006:	DMA Number of lines	(Must match to stay in sync)
//	008:	Frame base address	(May not wrap across memory)
//	00c:	(Frame base address, upper word--not used in this sim)
//	010:RO	Measured pixel clock frequency
//	014:	Pixel to bitmap mapping, and do we know the dims of our img
//		bit 31: Video dimensions appear to have stabilized, and two
//			frames in a row have calculated the same dimensions
//		bits 1-0: Control how pixels are encoded into memory, whether
//			24-bits per color, 16-bits per color, or 8-bits per
//			color.
//	015:	(Reserved)
//	018:	(Reserved)
//	01c:RO	Current frame rate
//	020:RO	Horizontal image size (pixel width)
//	022:RO	Vertical image size (pixel height)
//	024:RO	Distances from pixels to sync
//	028:RO	Sync duration
//	02c:RO	Raw clocks per row
//	02c:RO	Raw row periods per frame
//	030+:	(Reserved, may be mapped onto otherr addresses)
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2018-2024, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
// }}}
module	axicamera #(
		// {{{
		localparam	C_AXIL_ADDR_WIDTH = 6,
		localparam	C_AXIL_DATA_WIDTH = 32,
		parameter	C_AXI_ADDR_WIDTH = 40,
		parameter	C_AXI_DATA_WIDTH = 64,
		parameter	C_AXI_ID_WIDTH = 1,
		localparam	AXILLSB = $clog2(C_AXIL_DATA_WIDTH/8),
		//
		// AXI_ID
		// {{{
		// All AXI (full) master transactions will be conducted using
		// this ID.
		parameter [C_AXI_ID_WIDTH-1:0]	AXI_ID = 0,
		// }}}
		//
		// SYS_CLOCK_FREQUENCY - in Hz
		// {{{
		// Used to measure the pixel clock rate in reference to the
		// system clock rate.
		parameter	SYS_CLOCK_FREQUENCY = 100_000_000,
		// }}}
		//
		// LGFIFO - the log (based two) of the size of the FIFO within
		// {{{
		// the DMA.  Must be at least 9 (512 words).
		parameter	LGFIFO = 10,
		// }}}
		//
		// LGAFIFO - the log (based two) of the size of the asynchronous
		// {{{
		// FIFO.  Only need a small FIFO is needed here--just big
		// enough to cross clock domains.  There's already a much
		// bigger FIFO inside the AXICAMERA component that follows
		parameter	LGAFIFO= 5,
		//
		// OPT_LOWPOWER
		// {{{
		// If set, OPT_LOWPOWER includes logic to set any unused signals
		// to zero.
		parameter [0:0]	OPT_LOWPOWER = 1'b0
		// }}}
		// }}}
		// }}}
	) (
		// {{{
		input	wire				S_AXI_ACLK,
		// Verilator lint_off SYNCASYNCNET
		input	wire				S_AXI_ARESETN,
		// Verilator lint_on  SYNCASYNCNET
		//
		// The video input port
		// {{{
		input	wire				i_pix_clk,
		input	wire 				i_pix_valid,
		input	wire [23:0]			i_pixel,
		input	wire				i_hsync,
		input	wire				i_vsync,
		// }}}
		// The AXI-Lite control port
		// {{{
		input	wire				S_AXIL_AWVALID,
		output	wire				S_AXIL_AWREADY,
		input	wire [C_AXIL_ADDR_WIDTH-1:0]	S_AXIL_AWADDR,
		input	wire	[2:0]			S_AXIL_AWPROT,
		//
		input	wire				S_AXIL_WVALID,
		output	wire				S_AXIL_WREADY,
		input	wire [C_AXIL_DATA_WIDTH-1:0]	S_AXIL_WDATA,
		input	wire [C_AXIL_DATA_WIDTH/8-1:0]	S_AXIL_WSTRB,
		//
		output	reg				S_AXIL_BVALID,
		input	wire				S_AXIL_BREADY,
		output	reg	[1:0]			S_AXIL_BRESP,
		//
		input	wire				S_AXIL_ARVALID,
		output	wire				S_AXIL_ARREADY,
		input	wire [C_AXIL_ADDR_WIDTH-1:0]	S_AXIL_ARADDR,
		input	wire	[2:0]			S_AXIL_ARPROT,
		//
		output	reg				S_AXIL_RVALID,
		input	wire				S_AXIL_RREADY,
		output	reg [C_AXIL_DATA_WIDTH-1:0]	S_AXIL_RDATA,
		output	reg	[1:0]			S_AXIL_RRESP,
		// }}}
		// The AXI Master DMA (write) port
		// {{{
		output	wire				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	wire [C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
		output	wire [C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		output	wire	[7:0]			M_AXI_AWLEN,
		output	wire	[2:0]			M_AXI_AWSIZE,
		output	wire	[1:0]			M_AXI_AWBURST,
		output	wire				M_AXI_AWLOCK,
		output	wire	[3:0]			M_AXI_AWCACHE,
		output	wire	[2:0]			M_AXI_AWPROT,
		output	wire	[3:0]			M_AXI_AWQOS,
		//
		output	wire				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
		output	wire [C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		output	wire 				M_AXI_WLAST,
		//
		//
		input	wire				M_AXI_BVALID,
		output	wire				M_AXI_BREADY,
		input	wire [C_AXI_ID_WIDTH-1:0]	M_AXI_BID,
		input	wire	[1:0]			M_AXI_BRESP,
		// }}}
		// An unused AXI (master) read port, ...
		// {{{
		// just to complete the connections
		output	wire				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	wire [C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
		output	wire [C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		output	wire	[7:0]			M_AXI_ARLEN,
		output	wire	[2:0]			M_AXI_ARSIZE,
		output	wire	[1:0]			M_AXI_ARBURST,
		output	wire				M_AXI_ARLOCK,
		output	wire	[3:0]			M_AXI_ARCACHE,
		output	wire	[2:0]			M_AXI_ARPROT,
		output	wire	[3:0]			M_AXI_ARQOS,
		//
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		input	wire [C_AXI_ID_WIDTH-1:0]	M_AXI_RID,
		input	wire [C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire 				M_AXI_RLAST,
		input	wire	[1:0]			M_AXI_RRESP
		// }}}
		// }}}
	);

	// Register declarations
	// {{{
	// Verilator lint_off SYNCASYNCNET
	reg		video_reset;
	// Verilator lint_on  SYNCASYNCNET
	reg		r_pps;
	reg	[1:0]	reset_pipe;
	reg	[31:0]	sys_clk_frequency;
	reg	[31:0]	pps_counter;

	wire		pix_valid, pix_hlast, pix_vlast;
	wire	[23:0]	pix_data;

	wire				pixw_valid, pixw_hlast, pixw_vlast;
	wire	[C_AXI_DATA_WIDTH-1:0]	pixw_data;

	wire				pixb_valid, pixb_ready, pixb_vlast,
					pixb_hlast, pixb_empty;
	wire	[C_AXI_DATA_WIDTH-1:0]	pixb_data;

	wire	ign_fifo_full;

	wire		pix_locked;
	reg	[15:0]	pix_imwidth, pix_imhfront, pix_imhsync, pix_imwidth_raw;
	reg	[15:0]	pix_imheight,pix_imvfront, pix_imvsync,pix_imheight_raw;

	wire		bus_locked;
	wire	[15:0]	bus_imwidth, bus_imhfront, bus_imhsync, bus_imwidth_raw;
	wire	[15:0]	bus_imheight,bus_imvfront, bus_imvsync,bus_imheight_raw;

	reg				axil_write_ready, axil_read_ready,
					axil_read_valid, axil_bvalid;
	reg				read_staging, dma_read_flag;
	reg	[C_AXIL_DATA_WIDTH-1:0]	staging_data, axil_read_data;
	wire	[C_AXIL_DATA_WIDTH-1:0]	dmactl_rdata;

	reg	[8-1:0]			cfg_frame_rate_hz;
	reg	[1:0]			cfg_pixel_mapping;
	wire	[31:0]			cfg_pix_frequency;

	reg	[8:0]			r_frame_count;

	reg				dma_wvalid;
	reg				dmactl_awready_ignored,
					dmactl_wready_ignored,
					dmactl_bvalid_ignored,
					dmactl_arready_ignored,
					dmactl_rvalid_ignored;
	reg	[1:0]			dmactl_bresp_ignored,
					dmactl_rresp_ignored;
	reg	[1:0]			dma_waddr;
	reg	[C_AXIL_DATA_WIDTH-1:0]	dma_wdata;
	reg [C_AXIL_DATA_WIDTH/8-1:0]	dma_wstrb;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite Control
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Write signaling
	// {{{
	wire				awskd_valid;
	wire	[C_AXIL_ADDR_WIDTH-3:0]	awskd_addr;
	wire				wskd_valid;
	wire	[C_AXIL_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXIL_DATA_WIDTH/8-1:0]	wskd_strb;

	skidbuffer #(.OPT_OUTREG(0),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.DW(C_AXIL_ADDR_WIDTH-AXILLSB))
	axilawskid(//
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
		.i_data(S_AXIL_AWADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data(awskd_addr));

	skidbuffer #(.OPT_OUTREG(0),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.DW(C_AXIL_DATA_WIDTH + C_AXIL_DATA_WIDTH/8))
	axilwskid(//
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
		.i_data({ S_AXIL_WDATA, S_AXIL_WSTRB }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_data, wskd_strb }));

	assign	axil_write_ready = awskd_valid && wskd_valid
			&& (!S_AXIL_BVALID || S_AXIL_BREADY);

	initial	axil_bvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axil_bvalid <= 0;
	else if  (axil_write_ready)
		axil_bvalid <= 1;
	else if (S_AXIL_BREADY)
		axil_bvalid <= 0;

	assign	S_AXIL_BVALID = axil_bvalid;
	assign	S_AXIL_BRESP = 2'b00;
	// }}}

	// Read signaling
	// {{{
	wire				arskd_valid;
	wire	[C_AXIL_ADDR_WIDTH-3:0]	arskd_addr;

	skidbuffer #(.OPT_OUTREG(0),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.DW(C_AXIL_ADDR_WIDTH-AXILLSB))
	axilarskid(//
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXIL_ARVALID), .o_ready(S_AXIL_ARREADY),
		.i_data(S_AXIL_ARADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(arskd_valid), .i_ready(axil_read_ready),
		.o_data(arskd_addr));

	assign	axil_read_ready = arskd_valid
			&& (!axil_read_valid || !read_staging || S_AXIL_RREADY);

	assign	S_AXIL_RRESP = 2'b00;
	// }}}

	// Control register logic
	// {{{

	always @(posedge S_AXI_ACLK)
	begin
		dma_wvalid <= 0;
		dma_waddr  <= awskd_addr[1:0];
		dma_wdata  <= wskd_data;
		dma_wstrb  <= wskd_strb;

		if (axil_write_ready)
		case(awskd_addr[3:0])
		4'b0000: dma_wvalid <= 1;
		4'b0001: begin
			dma_wvalid <= 1;
			dma_wvalid <= 1;
			end
		4'b0010: dma_wvalid <= 1;
		4'b0011: dma_wvalid <= 1;
		//
		4'b0101: if (wskd_strb[0])
				cfg_pixel_mapping <= wskd_data[1:0];
		default: begin end
		endcase
	end

	always @(posedge S_AXI_ACLK)
	begin
		if (axil_read_ready)
		begin
			read_staging  <= 1;
			dma_read_flag <= 0;
			case(arskd_addr[3:0])
			4'b0000: dma_read_flag <= 1;
			4'b0001: dma_read_flag <= 1;
			4'b0010: dma_read_flag <= 1;
			4'b0011: dma_read_flag <= 1;
			4'b0100: staging_data <= cfg_pix_frequency;
			4'b0101: staging_data <= { bus_locked, 29'h0,
							cfg_pixel_mapping };
			// 4'b0110:
			4'b0111: staging_data[7:0] <= cfg_frame_rate_hz;
			4'b1000: staging_data <= { bus_imheight, bus_imwidth };
			4'b1001: staging_data <= { bus_imvfront, bus_imhfront };
			4'b1010: staging_data <= { bus_imvsync, bus_imhsync };
			4'b1011: staging_data <= { bus_imheight_raw,
							bus_imwidth_raw };
			default: begin end
			endcase
		end else begin
			if (!S_AXIL_RVALID || S_AXIL_RREADY)
				read_staging <= 0;
			dma_read_flag <= 0;
		end

		if (!S_AXI_ARESETN)
		begin
			read_staging <= 0;
			dma_read_flag <= 0;
		end
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axil_read_valid <= 0;
	else if (read_staging)
		axil_read_valid <= 1;
	else if (S_AXIL_RREADY)
		axil_read_valid <= 0;

	initial	axil_read_data = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXIL_RVALID || S_AXIL_RREADY)
	begin
		axil_read_data <= 0;

		case(dma_read_flag)
		1'b0: axil_read_data <= staging_data;
		1'b1: axil_read_data <= dmactl_rdata;
		endcase

		if (OPT_LOWPOWER && (!read_staging || !S_AXI_ARESETN))
			axil_read_data <= 0;
	end

	assign	S_AXIL_RVALID = axil_read_valid;
	assign	S_AXIL_RDATA  = axil_read_data;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Video reset
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	{ video_reset, reset_pipe } = -1;
	always @(posedge i_pix_clk or negedge S_AXI_ARESETN)
	if (!S_AXI_ARESETN)
		{ video_reset, reset_pipe } <= -1;
	else
		{ video_reset, reset_pipe } <= { reset_pipe, 1'b0 };
	
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//  Clock counting
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		sys_clk_frequency = SYS_CLOCK_FREQUENCY;

	initial	r_pps       = 1;
	initial	pps_counter = 0;
	always @(posedge S_AXI_ACLK)
	if (r_pps)
	begin
		pps_counter <= sys_clk_frequency;
		r_pps <= 0;
	end else begin
		pps_counter <= pps_counter - 1;
		r_pps <= (pps_counter <= 1);
	end

	clkcounter
	ckcounts(.i_sys_clk(S_AXI_ACLK), .i_sys_pps(r_pps),
		.i_tst_clk(i_pix_clk), .o_sys_counts(cfg_pix_frequency));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//  Video (pixel) processing
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Generate an AXI-stream of 24-bit pixels, with 2-metadata flags
	//
	sync2stream
	s2si(
		.i_clk(i_pix_clk), .i_reset(video_reset),
		.i_pix_valid(i_pix_valid), .i_hsync(i_hsync), .i_vsync(i_vsync),
		.i_pixel(i_pixel),
		//
		.M_AXIS_TVALID(pix_valid), .M_AXIS_TREADY(1'b1),
		.M_AXIS_TDATA(pix_data), .M_AXIS_TLAST(pix_vlast),
		.M_AXIS_TUSER(pix_hlast),
		//
		.o_width(pix_imwidth), .o_hfront(pix_imhfront),
		.o_hsync(pix_imhsync), .o_raw_width(pix_imwidth_raw),
		//
		.o_height(pix_imheight), .o_vfront(pix_imvfront),
		.o_vsync(pix_imvsync), .o_raw_height(pix_imheight_raw),
		//
		.o_locked(pix_locked)
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//  Move the image meta-data values from pixel to bus clock
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// _locked, _imwidth, _imheight
	// {{{
	tfrvalue #( .NB(1+32)
	) tfrsz (.i_aclk(i_pix_clk), .i_value({ pix_locked, pix_imwidth, pix_imheight }),
		.i_bclk(S_AXI_ACLK), .o_value({ bus_locked, bus_imwidth, bus_imheight })
	);
	// }}}

	// imwidth_raw, imheight_raw
	// {{{
	tfrvalue #(.NB(32)
	) tfrraw(.i_aclk(i_pix_clk), .i_value(
				{ pix_imwidth_raw, pix_imheight_raw }),
		.i_bclk(S_AXI_ACLK), .o_value(
				{ bus_imwidth_raw, bus_imheight_raw })
	);
	// }}}

	// _imhfront, _imvfront
	// {{{
	tfrvalue #( .NB(32)
	) tfrporch (.i_aclk(i_pix_clk), .i_value({ pix_imhfront, pix_imvfront }),
		.i_bclk(S_AXI_ACLK), .o_value({ bus_imhfront, bus_imvfront })
	);
	// }}}

	// _imhsync, _imvsync
	// {{{
	tfrvalue #( .NB(32)
	) tfrsync (.i_aclk(i_pix_clk), .i_value({ pix_imhsync, pix_imvsync }),
		.i_bclk(S_AXI_ACLK), .o_value({ bus_imhsync, bus_imvsync })
	);
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//  24b color to bus word mapping
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Transform the data stream from a 24-bit pixel stream to a raw
	// byte stream, having the width of the data bus
	wire	pix_ready;

	pix2stream #(
		.BUS_DATA_WIDTH(C_AXI_DATA_WIDTH)
	) p2si (
		.i_clk(i_pix_clk), .i_reset(video_reset),
		//
		.S_AXIS_TVALID(pix_valid), .S_AXIS_TREADY(pix_ready),
		.S_AXIS_TDATA(pix_data), .S_AXIS_TLAST(pix_hlast),
		.S_AXIS_TUSER(pix_vlast),
		//
		.M_AXIS_TVALID(pixw_valid), .M_AXIS_TREADY(1'b1),
		.M_AXIS_TDATA(pixw_data), .M_AXIS_TLAST(pixw_hlast),
		.M_AXIS_TUSER(pixw_vlast),
		//
		.i_mode(cfg_pixel_mapping)
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//  Asynchronous FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Pixels are generated in the pixel clock domain.  Data is consumed
	// below in the bus clock domain.  This asynchronous FIFO crosses
	// between the two domains from one to the other.
	//
	// ISSUE:
	//	There is a risk in this crossing that the FIFO will get
	// 	overloaded, and worse that this overloading will interfere with
	//	the bus clock domains attempts to synch to the incoming data.
	//	To be dealt with still.
	//
	//	Perhaps this asynchronous FIFO should be merged into the
	//	FIFO within the bus?  Then lost sync detection would be easier
	//	to determine ...
	afifo #(
		.LGFIFO(LGAFIFO), .WIDTH(2 + C_AXI_DATA_WIDTH)
	) pixfifo (
		.i_wclk(i_pix_clk), .i_wr_reset_n(!video_reset),
		.i_wr(pixw_valid),
		.i_wr_data({ pixw_vlast, pixw_hlast, pixw_data }),
		.o_wr_full(ign_fifo_full),
		//
		.i_rclk(S_AXI_ACLK), .i_rd_reset_n(S_AXI_ARESETN),
		.i_rd(pixb_valid && pixb_ready),
		.o_rd_data({ pixb_vlast, pixb_hlast, pixb_data }),
		.o_rd_empty(pixb_empty)
	);

	assign	pixb_valid = !pixb_empty;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Measure the frame rate
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	r_frame_count = 0;
	always @(posedge S_AXI_ACLK)
	if (r_pps)
		r_frame_count <= 0;
	else if (pixw_valid && pixw_vlast && !r_frame_count[8])
		r_frame_count <= r_frame_count + 1;

	always @(posedge S_AXI_ACLK)
	if (r_pps)
	begin
		if (r_frame_count[8])
			// Counter overflow--saturate the measurement
			cfg_frame_rate_hz <= -1;
		else
			cfg_frame_rate_hz <= r_frame_count[7:0];
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//  AXI Frame writer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	axivcamera #(
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.OPT_LGFIFO(LGFIFO),
		.AXI_ID(AXI_ID)
	) axidma (
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXIS_TVALID(pixb_valid), .S_AXIS_TREADY(pixb_ready),
		.S_AXIS_TDATA( pixb_data),  .S_AXIS_TLAST( pixb_vlast),
		.S_AXIS_TUSER( pixb_hlast),
		//
		// AXI-Lite control interface
		// {{{
		.S_AXIL_AWVALID(dma_wvalid),
		.S_AXIL_AWREADY(dmactl_awready_ignored),
		.S_AXIL_AWADDR( { dma_waddr, 2'b00 }),
		.S_AXIL_AWPROT( 3'b000),
		//
		.S_AXIL_WVALID(dma_wvalid),
		.S_AXIL_WREADY(dmactl_wready_ignored),
		.S_AXIL_WDATA( dma_wdata),
		.S_AXIL_WSTRB( dma_wstrb),
		//
		.S_AXIL_BVALID(dmactl_bvalid_ignored),
		.S_AXIL_BREADY(1'b1),
		.S_AXIL_BRESP( dmactl_bresp_ignored),
		//
		.S_AXIL_ARVALID(arskd_valid && arskd_addr[3:2] == 2'b00),
		.S_AXIL_ARREADY(dmactl_arready_ignored),
		.S_AXIL_ARADDR( {arskd_addr[1:0], 2'b00 }),
		.S_AXIL_ARPROT( 3'b000),
		//
		.S_AXIL_RVALID(dmactl_rvalid_ignored),
		.S_AXIL_RREADY(1'b1),
		.S_AXIL_RDATA( dmactl_rdata),
		.S_AXIL_RRESP( dmactl_rresp_ignored),
		// }}}
		// AXI (full) DMA Memory Write Interface
		// {{{
		.M_AXI_AWVALID(M_AXI_AWVALID),
		.M_AXI_AWREADY(M_AXI_AWREADY),
		.M_AXI_AWID(   M_AXI_AWID),
		.M_AXI_AWADDR( M_AXI_AWADDR),
		.M_AXI_AWLEN(  M_AXI_AWLEN),
		.M_AXI_AWSIZE( M_AXI_AWSIZE),
		.M_AXI_AWBURST(M_AXI_AWBURST),
		.M_AXI_AWLOCK( M_AXI_AWLOCK),
		.M_AXI_AWCACHE(M_AXI_AWCACHE),
		.M_AXI_AWPROT( M_AXI_AWPROT),
		.M_AXI_AWQOS(  M_AXI_AWQOS),
		//
		.M_AXI_WVALID(M_AXI_WVALID),
		.M_AXI_WREADY(M_AXI_WREADY),
		.M_AXI_WDATA( M_AXI_WDATA),
		.M_AXI_WSTRB( M_AXI_WSTRB),
		.M_AXI_WLAST( M_AXI_WLAST),
		//
		.M_AXI_BVALID(M_AXI_BVALID),
		.M_AXI_BREADY(M_AXI_BREADY),
		.M_AXI_BID(   M_AXI_BID),
		.M_AXI_BRESP( M_AXI_BRESP)
		// }}}
	);

	// Tie off the unused bus interface
	assign	M_AXI_ARVALID = 1'b0;
	assign	M_AXI_ARID    = AXI_ID;
	assign	M_AXI_ARADDR  = 0;
	assign	M_AXI_ARLEN   = 8'h0;
	assign	M_AXI_ARSIZE  = M_AXI_AWSIZE;
	assign	M_AXI_ARBURST = 2'b01;
	assign	M_AXI_ARLOCK  = 1'b0;
	assign	M_AXI_ARCACHE = 4'h0;
	assign	M_AXI_ARPROT  = 3'h0;
	assign	M_AXI_ARQOS   = 4'h0;
	//
	assign	M_AXI_RREADY  = 1'b1;
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0,
		S_AXIL_AWADDR[1:0], S_AXIL_ARADDR[1:0],
		S_AXIL_AWPROT, S_AXIL_ARPROT, ign_fifo_full,
		dmactl_awready_ignored, dmactl_wready_ignored,
		dmactl_bvalid_ignored,
		dmactl_arready_ignored, dmactl_rvalid_ignored,
		dmactl_bresp_ignored,   dmactl_rresp_ignored,
		M_AXI_ARREADY, M_AXI_RVALID, M_AXI_RID, M_AXI_RDATA,
			M_AXI_RLAST, M_AXI_RRESP,
		pix_ready, 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
