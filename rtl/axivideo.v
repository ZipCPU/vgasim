////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	AXIVIDEO
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	
//
// Registers:	
// {{{
//	000:	Memory Controller
//	004:	(Read only, bytes per line)
//	006:	(Read only, number of lines)
//	008:	Frame base address
//	00c:	Pixel control
//		Sets the pixel size
//	010:	Clock control (when enabled)
//		Controls the speed of the arbitrary clock generator
//	014:	(Reserved)
//	018:	(Reserved)
//	01c:	(Reserved)
//	020:	Horizontal image size (pixel width)
//	022:	Vertical   image size (pixel height)
//	024:	Horizontal porch duration (Distance from pixels to sync)
//	026:	Vertical   porch duration
//	028:	Horizontal sync duration
//	02a:	Vertical   sync duration
//	02c:	Horizontal pixel clocks per image line
//	02e:	Vertical   lines per frame
//	030:	(Reserved, may be mapped onto other addresses)
//	-3fc
//	400:	Color table begins
//	-x7fc
// }}}
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2022, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
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
`default_nettype	none
// `define	HDMI
//
// }}}
module	axivideo #(
		// {{{
		//
		// Size of the AXI (memory bus).  These are to be determined
		// by the size of the bus in your environment, and need to be
		// set acccordingly.  In general, bigger is better up to the
		// actual data width your memory device can support.
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter	C_AXI_ID_WIDTH = 1,
		//
		// Defines the maximum AXI burst size.  For AXI4, this should
		// be set to 8 for maximum performance.  For AXI3 backwards
		// compatibility, set this to 4.
`ifdef	AXI3
		parameter	OPT_LGMAXBURST = 4,
`else
		parameter	OPT_LGMAXBURST = 8,
`endif
		//
		// DEF_ACTIVE_ON_RESET: If true, immediately starts the video
		// on reset.  Useful for those designs that might never want
		// to turn it off, or not have external control over the
		// design.
		parameter [0:0]	DEF_ACTIVE_ON_RESET = 0,
		//
		// Initialize the number of lines per frame to this value on
		// reset
		parameter [15:0]	DEF_LINES_PER_FRAME = 1024,
		//
		// Initialize the number of words per line to this value on
		// reset.
		parameter [16-ADDRLSB-1:0] DEF_WORDS_PER_LINE
						= (1280 * 32)/C_AXI_DATA_WIDTH,
		//
		// Default colormapping mode.  Also sets the number of bits
		// per pixel--see the pixel mapper for more information.  The
		// default mode, 3'b111, is a 32-bits per pixel mode where the
		// top 8-bits are ignored.  (No alpha is supported)
		// parameter [2:0]	DEF_PIXEL_MODE = 3'b111,
		//
		// DEF_FRAMEADDR: the default AXI address of the frame buffer
		// containing video memory.  Unless OPT_UNALIGNED is set, this
		// should be aligned so that DEF_FRAMEADDR[ADDRLSB-1:0] == 0.
		parameter [C_AXI_ADDR_WIDTH-1:0]	DEF_FRAMEADDR = 0,
		//
		// The (log-based two of  the) size of the DMA FIFO in words.
		// I like to set this to the size of two AXI bursts, so that
		// while one is being read out the second can be read in.  Can
		// also be set larger if desired.
		parameter	LGFIFO = OPT_LGMAXBURST+1,
		//
		// AXI_ID is the ID we will use for all of our AXI transactions
		parameter	AXI_ID = 0,
		parameter [0:0]	OPT_EXTERNAL = 1'b1,
		//
		// xMODE_WIDTH is the number of bits required to hold the
		// various mode numbers
		parameter	HMODE_WIDTH = 12,
		parameter	VMODE_WIDTH = 12,
		//
		// OPT_GENCLK: Set to '1' to include control for the arbitrary
		// clock rate generation circuitry, zero if you'd rather
		// generate the pixel clock some other way
		parameter [0:0]	OPT_GENCLK = 1'b0,
		//
		// Size of the AXI-lite bus.  These are fixed, since 1) AXI-lite
		// is fixed at a width of 32-bits by Xilinx def'n, and 2) since
		// we only ever have 4 configuration words.
		localparam	C_AXIL_ADDR_WIDTH = 11,
		localparam	C_AXIL_DATA_WIDTH = 32,
		parameter [0:0]	OPT_LOWPOWER = 0,
		localparam	AXILLSB = $clog2(C_AXIL_DATA_WIDTH)-3,
		localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		// Verilator lint_off SYNCASYNCNET
		input	wire					S_AXI_ARESETN,
		// Verilator lint_on  SYNCASYNCNET
		//
		// The control interface
		// {{{
		input	wire					S_AXIL_AWVALID,
		output	wire					S_AXIL_AWREADY,
		input	wire	[C_AXIL_ADDR_WIDTH-1:0]		S_AXIL_AWADDR,
		input	wire	[2:0]				S_AXIL_AWPROT,
		//
		input	wire					S_AXIL_WVALID,
		output	wire					S_AXIL_WREADY,
		input	wire	[C_AXIL_DATA_WIDTH-1:0]		S_AXIL_WDATA,
		input	wire	[C_AXIL_DATA_WIDTH/8-1:0]	S_AXIL_WSTRB,
		//
		output	wire					S_AXIL_BVALID,
		input	wire					S_AXIL_BREADY,
		output	wire	[1:0]				S_AXIL_BRESP,
		//
		input	wire					S_AXIL_ARVALID,
		output	wire					S_AXIL_ARREADY,
		input	wire	[C_AXIL_ADDR_WIDTH-1:0]		S_AXIL_ARADDR,
		input	wire	[2:0]				S_AXIL_ARPROT,
		//
		output	wire					S_AXIL_RVALID,
		input	wire					S_AXIL_RREADY,
		output	wire	[C_AXIL_DATA_WIDTH-1:0]		S_AXIL_RDATA,
		output	wire	[1:0]				S_AXIL_RRESP,
		// }}}
		//
		// The AXI (full) read interface
		// {{{
		output	wire				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		output	wire	[7:0]			M_AXI_ARLEN,
		output	wire	[2:0]			M_AXI_ARSIZE,
		output	wire	[1:0]			M_AXI_ARBURST,
`ifdef	AXI3
		output	wire	[1:0]			M_AXI_ARLOCK,
`else
		output	wire				M_AXI_ARLOCK,
`endif
		output	wire	[3:0]			M_AXI_ARCACHE,
		output	wire	[2:0]			M_AXI_ARPROT,
		output	wire	[3:0]			M_AXI_ARQOS,
		//
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire				M_AXI_RLAST,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_RID,
		input	wire	[1:0]			M_AXI_RRESP,
		// }}}
		//
		// The external video processing pipeline interface
		// {{{
		// Outgoing / Master
		output	wire		M_VID_ACLK,
		output	wire		M_VID_ARESETN,
		//
		output	wire		M_VID_TVALID,
		input	wire		M_VID_TREADY,
		output	wire	[23:0]	M_VID_TDATA,
		output	wire		M_VID_TUSER,
		output	wire		M_VID_TLAST,
		// Incoming / slave
		input	wire		S_VID_TVALID,
		output	wire		S_VID_TREADY,
		input	wire	[23:0]	S_VID_TDATA,
		input	wire		S_VID_TUSER,
		input	wire		S_VID_TLAST,
		// }}}
		//
		// The video interface
		// {{{
		input	wire		i_pixclk,
		output	wire	[7:0]	o_clock_word,
`ifdef	HDMI
		output	wire	[9:0]	o_hdmi_red,
		output	wire	[9:0]	o_hdmi_grn,
		output	wire	[9:0]	o_hdmi_blu
`else
		output	wire		o_vga_vsync, o_vga_hsync,
		output	wire	[7:0]	o_vga_red,
		output	wire	[7:0]	o_vga_grn,
		output	wire	[7:0]	o_vga_blu
`endif
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	wire	i_clk   =  S_AXI_ACLK;
	wire	i_reset = !S_AXI_ARESETN;

	wire	arskd_valid;
	wire	awskd_valid, wskd_valid;

	wire				axil_write_ready;
	wire	[C_AXIL_ADDR_WIDTH-AXILLSB-1:0]	awskd_addr;
	//
	wire	[C_AXIL_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXIL_DATA_WIDTH/8-1:0]	wskd_strb;
	reg				axil_bvalid;
	//
	wire				axil_read_ready;
	wire	[C_AXIL_ADDR_WIDTH-AXILLSB-1:0]	arskd_addr;
	reg	[C_AXIL_DATA_WIDTH-1:0]	axil_read_data;
	reg				axil_read_valid;

	wire				mem_hsync, mem_vsync,
					mem_tvalid, mem_tready,
					afifo_empty, afifo_full;
	wire	[C_AXI_DATA_WIDTH-1:0]	mem_data;
	// Verilator lint_off  SYNCASYNCNET
	reg				pix_reset_n;
	// Verilator lint_on  SYNCASYNCNET
	reg	[1:0]			pix_reset_pipe;

	reg				dma_wvalid;
	reg	[3:0]			dma_awaddr;
	wire				dma_awready, dma_wready;
	reg	[C_AXIL_DATA_WIDTH-1:0]	dma_wdata;
	reg [C_AXIL_DATA_WIDTH/8-1:0]	dma_wstrb;
	wire				dma_bvalid;
	wire	[1:0]			dma_bresp;
	reg				dma_arvalid;
	wire				dma_arready;
	wire				dma_rvalid;
	reg [C_AXIL_DATA_WIDTH-1:0]	dma_rdata;
	wire	[1:0]			dma_rresp;

	reg	[1:0]			new_image_dimension;

	reg	[2:0]			cmap_mode;

	reg	[HMODE_WIDTH-1:0]	hm_width,  hm_porch, hm_synch, hm_raw;
	reg	[VMODE_WIDTH-1:0]	vm_height, vm_porch, vm_synch, vm_raw;
	reg	[HMODE_WIDTH-1:0]	words_per_line;
	reg				read_staging;

	wire		clk_stb;
	reg	[31:0]	clk_speed;
	reg		cmap_rd;
	reg	[31:0]	staging_data, dma_return_data, cmap_return_data;
	wire	[23:0]	cmap_rdata;
	reg	[7:0]	cmap_waddr;
	reg	[3:0]	dma_araddr;
	reg	[31:0]	new_image_size, new_image_porch, new_image_synch,
			new_image_raw;
	wire	[C_AXIL_DATA_WIDTH-1:0]	new_clk_speed;
	reg	[31:0]	image_size, image_porch, image_synch, image_raw;
	reg	[1:0]	staging_addr;
	reg		cmap_read_flag, dma_read_flag;
	reg		new_mode;

	wire				cmap_hsync, cmap_vsync, cmap_read;
	wire	[C_AXI_DATA_WIDTH-1:0]	cmap_data;
	wire		pix_valid, pix_ready, pix_hsync, pix_vsync;
	wire	[23:0]	pixel;

	wire		vin_valid, vin_ready, vin_hsync, vin_vsync;
	wire	[23:0]	vin_data;


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite signaling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Write signaling
	//
	// {{{
	skidbuffer #(
		// {{{
		.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXIL_ADDR_WIDTH-AXILLSB)
		// }}}
	)
	axilawskid(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
		.i_data(S_AXIL_AWADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data(awskd_addr)
		// }}}
	);

	skidbuffer #(
		// {{{
		.OPT_OUTREG(0),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.DW(C_AXIL_DATA_WIDTH+C_AXIL_DATA_WIDTH/8)
		// }}}
	) axilwskid(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
		.i_data({ S_AXIL_WDATA, S_AXIL_WSTRB }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_data, wskd_strb })
		// }}}
	);

	assign	axil_write_ready = awskd_valid && wskd_valid
			&& (!S_AXIL_BVALID || S_AXIL_BREADY)
			&& (new_image_dimension == 0);

	initial	axil_bvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_bvalid <= 0;
	else if (axil_write_ready)
		axil_bvalid <= 1;
	else if (S_AXIL_BREADY)
		axil_bvalid <= 0;

	assign	S_AXIL_BVALID = axil_bvalid;
	assign	S_AXIL_BRESP = 2'b00;
	// }}}

	//
	// Read signaling
	//
	// {{{


	skidbuffer #(
		// {{{
		.OPT_OUTREG(0),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.DW(C_AXIL_ADDR_WIDTH-AXILLSB)
		// }}}
	) axilarskid(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_ARVALID), .o_ready(S_AXIL_ARREADY),
		.i_data(S_AXIL_ARADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(arskd_valid), .i_ready(axil_read_ready),
		.o_data(arskd_addr)
		// }}}
	);

	assign	axil_read_ready = arskd_valid
			&& (!axil_read_valid || !read_staging || S_AXIL_RREADY);

	// assign	S_AXIL_RVALID = axil_read_valid;
	// assign	S_AXIL_RDATA  = axil_read_data;
	assign	S_AXIL_RRESP = 2'b00;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite register logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign new_clk_speed = apply_wstrb(clk_speed,wskd_data,wskd_strb);

	always @(*)
	begin

		image_size = 0;
		image_size[ 0 +: HMODE_WIDTH] = hm_width;
		image_size[16 +: VMODE_WIDTH] = vm_height;

		new_image_size = apply_wstrb(image_size, wskd_data, wskd_strb);
		new_image_size[31 : 16+VMODE_WIDTH] = 0;
		new_image_size[15 : HMODE_WIDTH] = 0;

		image_porch = 0;
		image_porch[ 0 +: HMODE_WIDTH] = hm_porch;
		image_porch[16 +: VMODE_WIDTH] = vm_porch;

		new_image_porch = apply_wstrb(image_porch,wskd_data, wskd_strb);
		new_image_porch[31:16+VMODE_WIDTH] = 0;
		new_image_porch[15:HMODE_WIDTH] = 0;

		image_synch = 0;
		image_synch[ 0 +: HMODE_WIDTH] = hm_synch;
		image_synch[16 +: VMODE_WIDTH] = vm_synch;

		new_image_synch = apply_wstrb(image_synch,wskd_data, wskd_strb);
		new_image_synch[15:HMODE_WIDTH] = 0;
		new_image_synch[31:16+VMODE_WIDTH] = 0;

		image_raw = 0;
		image_raw[ 0 +: HMODE_WIDTH] = hm_raw;
		image_raw[16 +: VMODE_WIDTH] = vm_raw;

		new_image_raw = apply_wstrb(image_raw,wskd_data, wskd_strb);
		new_image_raw[15:HMODE_WIDTH] = 0;
		new_image_raw[31:16+VMODE_WIDTH] = 0;
	end

//	020:	Horizontal image size (pixel width)
//	022:	Vertical   image size (pixel width)
//	024:	Horizontal porch duration (Distance from pixels to sync)
//	026:	Vertical   porch duration
//	028:	Horizontal sync duration
//	02a:	Vertical   sync duration
//	02c:	Horizontal pixel clocks per image line
//	02e:	Vertical   pixel clocks per image line

	always @(*)
		cmap_rd = axil_read_ready && arskd_addr[8];

	always @(posedge i_clk)
	begin
		dma_wvalid <= 0;
		cmap_waddr <= awskd_addr[7:0];
		dma_awaddr <= { awskd_addr[1:0], 2'b00 };
		dma_wdata  <= wskd_data;
		dma_wdata  <= wskd_data;
		dma_wstrb  <= wskd_strb;
		new_image_dimension <= (new_image_dimension << 1);

		new_mode <= 0;
		//assign	axil_write_ready = awskd_valid && wskd_valid
			//&& (!S_AXI_BVALID || S_AXI_BREADY)
			//&& (new_image_dimension != 0);

		if (axil_write_ready && !awskd_addr[8])
		case(awskd_addr[3:0])
		4'b0000: begin
			dma_wvalid <= 1;
			dma_wdata  <= { 16'h0, wskd_data[15:0] };
			end
		4'b0001: begin
			dma_wvalid <= 1;
			dma_wdata <= 0;
			dma_wdata[31:16] <= wskd_data[31:16];
			dma_wdata[15: 0] <={2'b00, words_per_line, {(ADDRLSB){1'b0}} };
			end
		4'b0010: dma_wvalid <= 1;
		4'b0011: begin
			if (wskd_strb[0])
			begin
				cmap_mode <= wskd_data[2:0];
				new_image_dimension[0] <= 1;
			end end
		4'b0100: clk_speed <= new_clk_speed;
		4'b1000: begin
			new_image_dimension[0] <= 1;
			hm_width  <= new_image_size[ 0 +: HMODE_WIDTH];
			vm_height <= new_image_size[16 +: VMODE_WIDTH];
			new_mode <= 1;
			end
		4'b1001: begin
			hm_porch <= new_image_porch[ 0 +: HMODE_WIDTH];
			vm_porch <= new_image_porch[16 +: VMODE_WIDTH];
			new_mode <= 1;
			end
		4'b1010: begin
			hm_synch <= new_image_synch[ 0 +: HMODE_WIDTH];
			vm_synch <= new_image_synch[16 +: VMODE_WIDTH];
			new_mode <= 1;
			end
		4'b1011: begin
			hm_raw <= new_image_raw[ 0 +: HMODE_WIDTH];
			vm_raw <= new_image_raw[16 +: VMODE_WIDTH];
			new_mode <= 1;
			end
		default: begin end
		endcase

		if (new_image_dimension[1])
		begin
			dma_wvalid <= 1;
			dma_awaddr <= 4'b0100;
			dma_wstrb <= -1;
			dma_wdata <= 0;
			dma_wdata[16 +: VMODE_WIDTH] <= vm_height;
			dma_wdata[ADDRLSB +: HMODE_WIDTH] <= words_per_line;
		end

		dma_awaddr[1:0] <= 2'b00;

		if (!S_AXI_ARESETN)
		begin
			dma_wvalid <= 0;
			new_image_dimension <= 0;
			new_mode <= 1;
		end

		if (!OPT_GENCLK)
			clk_speed <= 0;
	end


	always @(posedge i_clk)
	if (new_image_dimension[0])
	case(cmap_mode)
	3'b000: words_per_line <= (hm_width + C_AXI_DATA_WIDTH-1)/C_AXI_DATA_WIDTH;
	3'b001: words_per_line <= (hm_width + C_AXI_DATA_WIDTH/2-1)/(C_AXI_DATA_WIDTH/2);
	3'b010: words_per_line <= (hm_width + C_AXI_DATA_WIDTH/4-1)/(C_AXI_DATA_WIDTH/4);
	3'b011: words_per_line <= (hm_width + C_AXI_DATA_WIDTH/4-1)/(C_AXI_DATA_WIDTH/4);
	3'b100: words_per_line <= (hm_width + C_AXI_DATA_WIDTH/8-1)/(C_AXI_DATA_WIDTH/8);
	3'b101: words_per_line <= (hm_width + C_AXI_DATA_WIDTH/8-1)/(C_AXI_DATA_WIDTH/8);
	3'b110: words_per_line <= (hm_width + C_AXI_DATA_WIDTH/16-1)/(C_AXI_DATA_WIDTH/16);
	3'b111: words_per_line <= (hm_width + C_AXI_DATA_WIDTH/32-1)/(C_AXI_DATA_WIDTH/32);
	endcase

	always @(*)
	begin
		dma_arvalid = 1'b1;
		dma_araddr  = { arskd_addr[1:0], 2'b00 };
	end

	always @(posedge i_clk)
	begin
		if (axil_read_ready)
		begin
			read_staging <= 1;

			staging_data <= 0;
			cmap_read_flag <= arskd_addr[8];
			casez(arskd_addr[3:0])
			4'b00??: begin
				dma_read_flag <= !arskd_addr[8];
				staging_addr <= { !arskd_addr[8], 1'b0 };
				end
			4'b1000: begin
				staging_data[ 0 +: HMODE_WIDTH] <= hm_width;
				staging_data[16 +: VMODE_WIDTH] <= vm_height;
				staging_addr <= { !arskd_addr[8], 1'b1 };
				end
			4'b1001: begin
				staging_data[ 0 +: HMODE_WIDTH] <= hm_porch;
				staging_data[16 +: VMODE_WIDTH] <= vm_porch;
				staging_addr <= { !arskd_addr[8], 1'b1 };
				end
			4'b1010: begin
				staging_data[ 0 +: HMODE_WIDTH] <= hm_synch;
				staging_data[16 +: VMODE_WIDTH] <= vm_synch;
				staging_addr <= { !arskd_addr[8], 1'b1 };
				end
			4'b1011: begin
				staging_data[ 0 +: HMODE_WIDTH] <= hm_raw;
				staging_data[16 +: VMODE_WIDTH] <= vm_raw;
				staging_addr <= { !arskd_addr[8], 1'b1 };
				end
			4'b11??: staging_addr <= { !arskd_addr[8], 1'b0 };
			default: begin end
			endcase
		end else begin
			if (!S_AXIL_RVALID || S_AXIL_RREADY)
				read_staging  <= 0;
			dma_read_flag <= 0;
			cmap_read_flag<= 0;
		end

		if (!S_AXI_ARESETN)
		begin
			read_staging   <= 0;
			dma_read_flag  <= 0;
			cmap_read_flag <= 0;
		end
	end

	always @(posedge i_clk)
	if (dma_read_flag)
		dma_return_data <= dma_rdata;

	always @(posedge i_clk)
	if (cmap_read_flag)
		cmap_return_data <= { 8'h00, cmap_rdata };

	initial	axil_read_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_read_valid <= 1'b0;
	else if (read_staging)
		axil_read_valid <= 1'b1;
	else if (S_AXIL_RREADY)
		axil_read_valid <= 1'b0;

	always @(posedge i_clk)
	if (!S_AXIL_RVALID || S_AXIL_RREADY)
	begin
		axil_read_data <= 0;

		casez(staging_addr)
		2'b1?: if (cmap_read_flag)
				axil_read_data <= { 8'h0, cmap_rdata };
			else
				axil_read_data <= cmap_return_data;
		2'b00: if (dma_read_flag)
				axil_read_data <= dma_rdata;
			else
				axil_read_data <= dma_return_data;
		2'b01: axil_read_data <= staging_data;
		endcase
	end

	assign	S_AXIL_RVALID = axil_read_valid;
	assign	S_AXIL_RDATA  = axil_read_data;

	function [C_AXI_DATA_WIDTH-1:0]	apply_wstrb;
		input	[C_AXI_DATA_WIDTH-1:0]		prior_data;
		input	[C_AXI_DATA_WIDTH-1:0]		new_data;
		input	[C_AXI_DATA_WIDTH/8-1:0]	wstrb;

		integer	k;
		for(k=0; k<C_AXI_DATA_WIDTH/8; k=k+1)
		begin
			apply_wstrb[k*8 +: 8]
				= wstrb[k] ? new_data[k*8 +: 8] : prior_data[k*8 +: 8];
		end
	endfunction
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reset the pixel clock domain
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	{ pix_reset_n, pix_reset_pipe } = 0;
	always @(posedge i_pixclk, negedge S_AXI_ARESETN)
	if (!S_AXI_ARESETN)
		{ pix_reset_n, pix_reset_pipe } <= 0;
	else begin
		{ pix_reset_n, pix_reset_pipe } <= { pix_reset_pipe, 1'b1 };
		if (new_mode)
			pix_reset_n <= 0;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock generator
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_GENCLK)
	begin : GENERATE_CLOCK
`ifdef	VERILATOR
		assign	o_clock_word = 0;
		assign	clk_stb = 0;
`else
		genclk
		videoclk(.i_clk(S_AXI_ACLK), .i_delay(clk_speed),
			.o_word(o_clock_word), .o_stb(clk_stb));
`endif
	end else begin : NO_CLOCK_CONTROL

		assign	o_clock_word = 0;
		assign	clk_stb = 0;

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXIVDMA
	// {{{
	// Read pixel/frame data from the AXI (memory) bus
	axivdisplay #(
		// {{{
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		//
		.OPT_LGMAXBURST(OPT_LGMAXBURST),
		//
		.DEF_ACTIVE_ON_RESET(DEF_ACTIVE_ON_RESET),
		.DEF_LINES_PER_FRAME(DEF_LINES_PER_FRAME),
		.DEF_WORDS_PER_LINE(DEF_WORDS_PER_LINE),
		.DEF_FRAMEADDR(DEF_FRAMEADDR),
		.LGFIFO(LGFIFO),
		.AXI_ID(AXI_ID)
		// }}}
	) videodma (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		// The video stream interface
		// {{{
		.M_AXIS_TVALID(mem_tvalid), .M_AXIS_TREADY(mem_tready),
			.M_AXIS_TDATA(mem_data),
			.M_AXIS_TLAST(mem_vsync), .M_AXIS_TUSER(mem_hsync),
		// }}}
		//
		// The (internal) AXI-lite control interface
		// {{{
		.S_AXIL_AWVALID(dma_wvalid), .S_AXIL_AWREADY(dma_awready),
		.S_AXIL_AWADDR(dma_awaddr), .S_AXIL_AWPROT(3'h0),
		//
		.S_AXIL_WVALID(dma_wvalid), .S_AXIL_WREADY(dma_wready),
			.S_AXIL_WDATA(dma_wdata), .S_AXIL_WSTRB(dma_wstrb),
		//
		.S_AXIL_BVALID(dma_bvalid), .S_AXIL_BREADY(1'b1),
			.S_AXIL_BRESP(dma_bresp),
		//
		.S_AXIL_ARVALID(dma_arvalid), .S_AXIL_ARREADY(dma_arready),
			.S_AXIL_ARADDR(dma_araddr), .S_AXIL_ARPROT(3'h0),
		//
		.S_AXIL_RVALID(dma_rvalid), .S_AXIL_RREADY(1'b1),
			.S_AXIL_RDATA(dma_rdata), .S_AXIL_RRESP(dma_rresp),
		// }}}
		//
		// The AXI (full) read interface
		// {{{
		.M_AXI_ARVALID(M_AXI_ARVALID), .M_AXI_ARREADY(M_AXI_ARREADY),
			.M_AXI_ARID(   M_AXI_ARID),.M_AXI_ARADDR( M_AXI_ARADDR),
			.M_AXI_ARLEN(M_AXI_ARLEN), .M_AXI_ARSIZE( M_AXI_ARSIZE),
			.M_AXI_ARBURST(M_AXI_ARBURST),
			.M_AXI_ARLOCK( M_AXI_ARLOCK),
			.M_AXI_ARCACHE(M_AXI_ARCACHE),
			.M_AXI_ARPROT( M_AXI_ARPROT),
			.M_AXI_ARQOS(  M_AXI_ARQOS),
		//
		.M_AXI_RVALID(M_AXI_RVALID), .M_AXI_RREADY(M_AXI_RREADY),
			.M_AXI_RDATA( M_AXI_RDATA), .M_AXI_RLAST( M_AXI_RLAST),
			.M_AXI_RID(   M_AXI_RID),   .M_AXI_RRESP( M_AXI_RRESP)
		// }}}
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Asynchronous FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	afifo #(
		// {{{
		.LGFIFO(5), .WIDTH(C_AXI_DATA_WIDTH+2)
		// }}}
	) switch_clocks(
		// {{{
		// Write (incoming) interface--bus clock
		.i_wclk(S_AXI_ACLK), .i_wr_reset_n(S_AXI_ARESETN),
		.i_wr(mem_tvalid && mem_tready),
			.i_wr_data({ mem_hsync, mem_vsync, mem_data }),
			.o_wr_full(afifo_full),
		//
		// Read (outgoing) interface--pixel clock
		.i_rclk(i_pixclk), .i_rd_reset_n(pix_reset_n),
		.i_rd(cmap_read),
			.o_rd_data({ cmap_hsync, cmap_vsync, cmap_data }),
			.o_rd_empty(afifo_empty)
		// }}}
	);

	assign	mem_tready = !afifo_full;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// vidstream2pix
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	vidstream2pix #(
		// {{{
		.BUS_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.OPT_MSB_FIRST(1'b0),
		.HMODE_WIDTH(HMODE_WIDTH)
		// }}}
	) s2pix(
		// {{{
		.i_clk(i_pixclk), .i_reset(!pix_reset_n),
		.S_AXIS_TVALID(!afifo_empty), .S_AXIS_TREADY(cmap_read),
		.S_AXIS_TDATA(cmap_data), .S_AXIS_TLAST(cmap_vsync),
			.S_AXIS_TUSER(cmap_hsync),
		.M_AXIS_TVALID(pix_valid), .M_AXIS_TREADY(pix_ready),
			.M_AXIS_TDATA(pixel), .M_AXIS_TLAST(pix_vsync),
			.M_AXIS_TUSER(pix_hsync),
		//
		// Colormap decoding interface
		.i_mode(cmap_mode), .i_pixels_per_line(hm_width),
		//
		// Colormap table interface
		.i_cmap_rd(cmap_rd),
			.i_cmap_raddr(arskd_addr[7:0]),
			.o_cmap_rdata(cmap_rdata),
		.i_cmap_we(awskd_valid && wskd_valid && awskd_addr[8]),
			.i_cmap_waddr(cmap_waddr),
			.i_cmap_wdata(dma_wdata[23:0]), .i_cmap_wstrb(dma_wstrb[2:0])
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Optional external video processing chain
	// {{{
	generate if (OPT_EXTERNAL)
	begin : GEN_EXTERNAL
		// {{{
		assign	M_VID_ACLK    = i_pixclk;
		assign	M_VID_ARESETN = pix_reset_n;

		assign	M_VID_TVALID = pix_valid;
		assign	pix_ready    = M_VID_TREADY;
		assign	M_VID_TDATA  = pixel;
		assign	M_VID_TLAST  = pix_vsync;
		assign	M_VID_TUSER  = pix_hsync;

		assign	vin_valid    = S_VID_TVALID;
		assign	S_VID_TREADY = vin_ready;
		assign	vin_data     = S_VID_TDATA;
		assign	vin_hsync    = S_VID_TUSER;
		assign	vin_vsync    = S_VID_TLAST;
		// }}}
	end else begin : GEN_INTERNAL_ONLY
		// {{{
		assign	M_VID_ACLK    = 1'b0;
		assign	M_VID_ARESETN = 1'b0;

		assign	M_VID_TVALID = 1'b0;
		assign	S_VID_TREADY = 1'b0;
		assign	M_VID_TDATA  = 0;
		assign	M_VID_TUSER  = 0;
		assign	M_VID_TLAST  = 0;

		assign	vin_valid = pix_valid;
		assign	pix_ready = vin_ready;
		assign	vin_data  = pixel;
		assign	vin_hsync = pix_hsync;
		assign	vin_vsync = pix_vsync;

		// Verilator lint_off UNUSED
		wire	unused_interface;
		assign	unused_interface = &{ 1'b0,
				S_VID_TVALID, M_VID_TREADY, S_VID_TDATA,
					S_VID_TUSER, S_VID_TLAST
				};
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Actual video logic generation
	// {{{
`ifdef	HDMI
	////////////////////////////////////////////////////////////////////////
	//
	// axis2hdmi
	// {{{
	axishdmi #(
		.HW(HMODE_WIDTH), .VW(VMODE_WIDTH)
	) genhdmi(
		// {{{
		.i_pixclk(i_pixclk), .i_reset(!pix_reset_n),
		//
		// Video stream interface
		// {{{
		.i_valid(vin_valid), .o_ready(vin_ready),
			.i_hlast(vin_hsync), .i_vlast(vin_vsync),
			.i_rgb_pix(vin_data),
		// }}}
		// Video mode information
		// {{{
		.i_hm_width(hm_width), .i_hm_porch(hm_porch),
			.i_hm_synch(hm_synch), .i_hm_raw(hm_raw),
		//
		.i_vm_height(vm_height), .i_vm_porch(vm_porch),
			.i_vm_synch(vm_synch), .i_vm_raw(vm_raw),
		// }}}
		// HDMI outputs
		.o_red(o_hdmi_red), .o_grn(o_hdmi_grn), .o_blu(o_hdmi_blu)
		// }}}
	);

	// }}}
`else
	////////////////////////////////////////////////////////////////////////
	//
	// axis2vga
	// {{{
	axisvga #(
		.HW(HMODE_WIDTH), .VW(VMODE_WIDTH)
	) genvga(
		// {{{
		.i_pixclk(i_pixclk), .i_reset(!pix_reset_n),
		//
		// Video stream interface
		// {{{
		.i_valid(vin_valid), .o_ready(vin_ready),
			.i_hlast(vin_hsync), .i_vlast(vin_vsync),
			.i_rgb_pix(vin_data),
		// }}}
		// Video mode information
		// {{{
		.i_hm_width(hm_width), .i_hm_porch(hm_porch),
			.i_hm_synch(hm_synch), .i_hm_raw(hm_raw),
		//
		.i_vm_height(vm_height), .i_vm_porch(vm_porch),
			.i_vm_synch(vm_synch), .i_vm_raw(vm_raw),
		// }}}
		// VGA outputs
		.o_vsync(o_vga_vsync), .o_hsync(o_vga_hsync),
		.o_red(o_vga_red), .o_grn(o_vga_grn), .o_blu(o_vga_blu)
		// }}}
	);
	// }}}
`endif
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXIL_AWPROT, S_AXIL_ARPROT, clk_stb,
			S_AXIL_ARADDR[AXILLSB-1:0],
			S_AXIL_AWADDR[AXILLSB-1:0], dma_rresp, dma_bresp,
			dma_rvalid, new_image_size, new_image_porch,
			new_image_synch, new_image_raw,
			dma_awready, dma_wready, dma_bvalid, dma_arready };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties used in verfiying (portions of) this core
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-lite control interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_AXIL_LGDEPTH = 4;
	wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
					faxil_wr_outstanding,
					faxil_awr_outstanding;

	faxil_slave #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_LGDEPTH(F_AXIL_LGDEPTH),
		.F_AXI_MAXWAIT(2),
		.F_AXI_MAXDELAY(2),
		.F_AXI_MAXRSTALL(3),
		.F_OPT_COVER_BURST(4)
		// }}}
	) faxil(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXIL_AWVALID),
		.i_axi_awready(S_AXIL_AWREADY),
		.i_axi_awaddr( S_AXIL_AWADDR),
		.i_axi_awcache(4'h0),
		.i_axi_awprot( S_AXIL_AWPROT),
		//
		.i_axi_wvalid(S_AXIL_WVALID),
		.i_axi_wready(S_AXIL_WREADY),
		.i_axi_wdata( S_AXIL_WDATA),
		.i_axi_wstrb( S_AXIL_WSTRB),
		//
		.i_axi_bvalid(S_AXIL_BVALID),
		.i_axi_bready(S_AXIL_BREADY),
		.i_axi_bresp( S_AXIL_BRESP),
		//
		.i_axi_arvalid(S_AXIL_ARVALID),
		.i_axi_arready(S_AXIL_ARREADY),
		.i_axi_araddr( S_AXIL_ARADDR),
		.i_axi_arcache(4'h0),
		.i_axi_arprot( S_AXIL_ARPROT),
		//
		.i_axi_rvalid(S_AXIL_RVALID),
		.i_axi_rready(S_AXIL_RREADY),
		.i_axi_rdata( S_AXIL_RDATA),
		.i_axi_rresp( S_AXIL_RRESP),
		//
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding)
		// }}}
		);

	always @(*)
	begin
		assert(faxil_awr_outstanding== (S_AXIL_BVALID ? 1:0)
			+(S_AXIL_AWREADY ? 0:1));
		assert(faxil_wr_outstanding == (S_AXIL_BVALID ? 1:0)
			+(S_AXIL_WREADY ? 0:1));

		assert(faxil_rd_outstanding == (S_AXIL_RVALID ? 1:0)
			+(S_AXIL_ARREADY ? 0:1));
	end

	//
	// Check that our low-power only logic works by verifying that anytime
	// S_AXI_RVALID is inactive, then the outgoing data is also zero.
	//
	always @(*)
	if (OPT_LOWPOWER && !S_AXI_RVALID)
		assert(S_AXI_RDATA == 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// While there are already cover properties in the formal property
	// set above, you'll probably still want to cover something
	// application specific here

	// }}}
`endif
// }}}
endmodule
