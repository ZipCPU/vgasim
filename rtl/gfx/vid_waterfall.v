////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/gfx/vid_waterfall.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Take an output stream, such as is from an FFT or other such,
//		and turn it into a falling raster display--with the newest data
//	at the top, and the display naturally scrolling vertically down as new
//	data arrives.
//
// Status: Although the initial design is done, it has some unreasonable
//	limitations:
//
//	1. It depends upon the data packet length (which determins *_TLAST)
//		coming into the IP having exactly the width of the video output.
//	2. It also requires that the design go through a reset in order to
//		change any video parameters.  This reset isn't (yet) handled
//		in the top level IP, although it should be.  (i.e., height,
//		width, or video address changes should trigger a reset of the
//		whole chain.
//	3. The input data is assumed to be synchronous with the bus, even
//		though this may not be the case.
//	4. There should be an external enable switch, to keep the IP from
//		trying to access memory prior to the configuration being set.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
`default_nettype	none
`define	WISHBONE
// }}}
module	vid_waterfall #(
		// {{{
		// parameter	LGNFFT  = 10,
		parameter	LGFRAME = 11,
		parameter	LGFIFO  = 7,
		parameter	PW  = 8,	// Pixel width
		localparam [0:0]	OPT_ASYNC_CLOCKS = 1'b1,
		parameter [0:0]	OPT_TUSER_IS_SOF = 1'b1,
`ifdef	WISHBONE
		parameter	AW = 32,
		parameter	DW = 32
`else
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		localparam	AW = C_AXI_ADDR_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH
`endif
		// }}}
	) (
		// {{{
		input	wire			i_pixclk,
		// Control wires
		// {{{
		input	wire	[AW-1:0]	i_baseaddr, i_lastaddr,
		input	wire [LGFRAME-1:0]	i_width, i_height,
		input	wire			i_en,
		// }}}
		// Incoming data stream
		// {{{
		input	wire		S_AXIS_TVALID,
		output	wire		S_AXIS_TREADY,
		input	wire [PW-1:0]	S_AXIS_TDATA,
		input	wire		S_AXIS_TLAST,
		// }}}
		// Bus interface
`ifdef	WISHBONE
		// Wishbone bus master
		// {{{
		input	wire		i_clk, i_reset,
		//
		output	wire			o_wb_cyc, o_wb_stb, o_wb_we,
		output	wire [AW-1:0]		o_wb_addr,
		output	wire [DW-1:0]		o_wb_data,
		output	wire [DW/8-1:0]		o_wb_sel,
		input	wire			i_wb_stall,
		input	wire			i_wb_ack,
		input	wire [DW-1:0]		i_wb_data,
		input	wire			i_wb_err,
		// }}}
`else // AXI-lite
		// AXI-Lite
		// {{{
		input	wire		S_AXI_ACLK, S_AXI_ARESETN,
		//
		output	wire		M_AXIL_AWVALID,
		output	wire		M_AXIL_AWREADY,
		output	wire [AW-1:0]	M_AXIL_AWADDR,
		output	wire [2:0]	M_AXIL_AWPROT,
		//
		output	wire		M_AXIL_WVALID,
		output	wire		M_AXIL_WREADY,
		output	wire [DW-1:0]	M_AXIL_WDATA,
		output	wire [DW/8-1:0]	M_AXIL_WSTRB,
		//
		output	wire		M_AXIL_BVALID,
		output	wire		M_AXIL_BREADY,
		output	wire [1:0]	M_AXIL_BRESP,
		//
		output	wire		M_AXIL_ARVALID,
		output	wire		M_AXIL_ARREADY,
		output	wire [AW-1:0]	M_AXIL_ARADDR,
		output	wire [1:0]	M_AXIL_ARPROT,
		//
		output	wire		M_AXIL_RVALID,
		output	wire		M_AXIL_RREADY,
		output	wire [DW-1:0]	M_AXIL_RDATA,
		output	wire [1:0]	M_AXIL_RRESP,
		// }}}
`endif
		// Outgoing video stream
		// {{{
		output	wire		M_VID_TVALID,
		input	wire		M_VID_TREADY,
		output	wire [PW-1:0]	M_VID_TDATA,
		output	wire		M_VID_TLAST,
		output	wire		M_VID_TUSER,
		// }}}
		output	reg	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	wire	bus_clk = i_clk;
	wire	bus_reset = i_reset;

	localparam [0:0] OPT_MSB_FIRST = 1'b1;
	wire			wr_cyc, wr_stb, wr_we;
	wire	[AW-1:0]	wr_addr;
	wire	[DW-1:0]	wr_data;
	wire	[DW/8-1:0]	wr_sel;
	wire			wr_ack, wr_stall, wr_err;

	wire			rd_cyc, rd_stb, rd_we;
	wire	[AW-1:0]	rd_addr;
	wire	[DW-1:0]	rd_data;
	wire	[DW/8-1:0]	rd_sel;
	wire			rd_ack, rd_stall, rd_err;

	wire	[AW-1:0]	w_first_addr;
	wire			read_err;

	wire	px_hlast, px_vlast, px_read, px_empty;
	wire	m_bus_pxread, m_bus_pxvlast, m_bus_pxhlast, m_bus_pxempty;
	reg		dbg_pix_reset, dbg_pix_reset_pipe;
	wire		m_bus_err, m_bus_valid, m_bus_ready, m_bus_tlast,
			m_bus_tuser;
	wire		ign_dbgafull, dbga_empty;


	// }}}

	vid_waterfall_w #(
		// {{{
		.AW(AW), .DW(DW), .PW(PW), .LGFRAME(LGFRAME),
		.LGFIFO(LGFIFO),
		.OPT_MSB_FIRST(OPT_MSB_FIRST)
		// }}}
	) write_mem (
		// {{{
		.i_clk(bus_clk), .i_reset(bus_reset),
		//
		.S_AXI_TVALID(S_AXIS_TVALID),
		.S_AXI_TREADY(S_AXIS_TREADY),
		.S_AXI_TDATA(S_AXIS_TDATA),
		.S_AXI_TLAST(S_AXIS_TLAST),
		//
		.i_height(i_height), .i_width(i_width),
		.i_baseaddr(i_baseaddr), .o_first_line(w_first_addr),
			.i_lastaddr(i_lastaddr),
		.i_en(i_en),
		//
		.o_wb_cyc(wr_cyc), .o_wb_stb(wr_stb), .o_wb_we(wr_we),
			.o_wb_addr(wr_addr), .o_wb_data(wr_data),
			.o_wb_sel(wr_sel),
		.i_wb_stall(wr_stall), .i_wb_ack(wr_ack),
			.i_wb_data({(DW){1'b0}}), .i_wb_err(wr_err)
		// }}}
	);

	vid_waterfall_r #(
		// {{{
		.AW(AW), .DW(DW), .PW(PW), .LGFRAME(LGFRAME),
		.LGFIFO(LGFIFO),
		.OPT_MSB_FIRST(OPT_MSB_FIRST),
		.OPT_ASYNC_CLOCKS(OPT_ASYNC_CLOCKS),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) read_mem (
		// {{{
		.i_clk(bus_clk), .i_pixclk(i_pixclk), .i_reset(bus_reset),
		//
		.i_height(i_height), .i_width(i_width),
		.i_baseaddr(i_baseaddr), .i_first_line(w_first_addr),
			.i_lastaddr(i_lastaddr),
		.i_en(i_en), .o_err(read_err),
		//
		.o_wb_cyc(rd_cyc), .o_wb_stb(rd_stb), .o_wb_we(rd_we),
			.o_wb_addr(rd_addr), .o_wb_data(rd_data),
			.o_wb_sel(rd_sel),
		.i_wb_stall(rd_stall), .i_wb_ack(rd_ack),
			.i_wb_data(i_wb_data), .i_wb_err(rd_err),
		//
		.M_VID_TVALID(M_VID_TVALID), .M_VID_TREADY(M_VID_TREADY),
		.M_VID_TDATA( M_VID_TDATA), .M_VID_TLAST( M_VID_TLAST),
		.M_VID_TUSER( M_VID_TUSER),
		//
		.o_dbg({ px_read, px_empty, px_vlast, px_hlast })
		// }}}
	);

	wbarbiter #(
		.DW(DW), .AW(AW)
	) arbiter (
		// {{{
		.i_clk(bus_clk), .i_reset(bus_reset),
		//
		.i_a_cyc(wr_cyc), .i_a_stb(wr_stb), .i_a_we(wr_we),
		.i_a_adr(wr_addr), .i_a_dat(wr_data), .i_a_sel(wr_sel),
		.o_a_stall(wr_stall), .o_a_ack(wr_ack), .o_a_err(wr_err),
		//
		.i_b_cyc(rd_cyc), .i_b_stb(rd_stb), .i_b_we(rd_we),
		.i_b_adr(rd_addr), .i_b_dat(rd_data), .i_b_sel(rd_sel),
		.o_b_stall(rd_stall), .o_b_ack(rd_ack), .o_b_err(rd_err),
		//
		.o_cyc(o_wb_cyc), .o_stb(o_wb_stb), .o_we(o_wb_we),
		.o_adr(o_wb_addr), .o_dat(o_wb_data), .o_sel(o_wb_sel),
		.i_stall(i_wb_stall), .i_ack(i_wb_ack), .i_err(i_wb_err)
		// }}}
	);

	////////////////////////////////////////////////////////////////////////
	//
	// Generate some debugging symbols--if needed
	// {{{
	always @(posedge i_pixclk or posedge bus_reset)
	if (bus_reset)
		{ dbg_pix_reset, dbg_pix_reset_pipe } <= -1;
	else
		{ dbg_pix_reset, dbg_pix_reset_pipe } <= { dbg_pix_reset_pipe, 1'b0 };

	afifo #(
		.LGFIFO(3), .WIDTH(9)
	) u_dbgafifo (
		// {{{
		.i_wclk(i_pixclk),
		.i_wr(1'b1),
		.i_wr_reset_n(!dbg_pix_reset),
		.i_wr_data({ px_empty, px_read, px_vlast, px_hlast,
				read_err, M_VID_TVALID, M_VID_TREADY,
					M_VID_TLAST, M_VID_TUSER }),
		.o_wr_full(ign_dbgafull),
		.i_rclk(bus_clk), .i_rd_reset_n(!bus_reset),
		.i_rd(1'b1), .o_rd_data(
			{ m_bus_pxempty, m_bus_pxread, m_bus_pxvlast, m_bus_pxhlast,
				m_bus_err, m_bus_valid, m_bus_ready,
					m_bus_tlast, m_bus_tuser }),
		.o_rd_empty(dbga_empty)
		// }}}
	);

	always @(posedge i_clk)
	begin
		o_debug <= 0;

		if (!dbga_empty)
		begin
			o_debug[7:3] <= { m_bus_err, m_bus_valid, m_bus_ready,
						m_bus_tlast, m_bus_tuser };
			o_debug[27:24] <= { m_bus_pxempty, m_bus_pxread,
						m_bus_pxhlast, m_bus_pxvlast };
		end else begin
			o_debug[7:3] <= o_debug[7:3];
			o_debug[27:24] <= o_debug[27:24];

			// If ready *was* high, drop valid
			if (o_debug[5])
				o_debug[6] <= 1'b0;
			// Since nothing is in the FIFO, ready must be low
			o_debug[5] <= 1'b0;
			// Everything else must either stay the same, or becomes
			// a don't care, so ... we'll keep it the same.
		end

		o_debug[2:0] <= {
			S_AXIS_TVALID,
			S_AXIS_TREADY,
			S_AXIS_TLAST };

		o_debug[12:8] <= { wr_cyc, wr_stb, wr_stall,
					wr_cyc && wr_ack, wr_cyc && wr_err };
		o_debug[17:13] <= { rd_cyc, rd_stb, rd_stall,
					rd_cyc && rd_ack, rd_cyc && rd_err };
		o_debug[23:18] <= { o_wb_cyc, o_wb_stb, o_wb_we, i_wb_stall,
					o_wb_cyc && i_wb_ack,
					o_wb_cyc && i_wb_err };
		o_debug[28] <= dbga_empty;
		o_debug[29] <= read_mem.last_ack;
		o_debug[30] <= (read_mem.wb_outstanding == 0);

		o_debug[31] <= m_bus_err && !o_debug[7];
	end
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ign_dbgafull };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
