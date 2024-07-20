////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/gfx/vid_split.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Draws a split screen display.  The top half will contain a
//		Spectrogram (trace), whereas the bottom half will contain a
//	waterfall display (falling raster), each with the (rough) same data
//	in it.
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
`default_nettype none
// }}}
module	vid_split #(
		// {{{
		localparam		PW = 24,
		parameter		AW = 28,	// Address width
		parameter		DW = 32,	// Bus data width
		parameter		IW = 8,
		parameter		LGFRAME = 12,
					LGNFFT = 10,
		parameter [0:0]		PIXEL = 0,
		parameter [0:0]		OPT_TUSER_IS_SOF = 1
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		input	wire			i_pixclk, i_pix_reset,
		//
		input	wire	[LGFRAME-1:0]	i_width, i_height,
		input	wire	[AW-1:0]	i_baseaddr, i_lastaddr,
		input	wire			i_en,
		output	wire	[2:0]		o_split_err,
		//
		input	wire			S_AXIS_TVALID,
		output	wire			S_AXIS_TREADY,
		input	wire	[IW-1:0]	S_AXIS_TDATA,
		input	wire			S_AXIS_TLAST,
		//
		output	wire			o_wb_cyc, o_wb_stb, o_wb_we,
		output	wire	[AW-1:0]	o_wb_addr,
		output	wire	[DW-1:0]	o_wb_data,
		output	wire	[DW/8-1:0]	o_wb_sel,
		input	wire			i_wb_stall,
		input	wire			i_wb_ack,
		input	wire	[DW-1:0]	i_wb_data,
		input	wire			i_wb_err,
		//
		output	wire			M_VID_VALID,
		input	wire			M_VID_READY,
		output	wire	[PW-1:0]	M_VID_DATA,
		output	wire			M_VID_LAST,
		output	wire			M_VID_USER,
		//
		output	wire	[31:0]		o_debug
		// }}}
	);

	// Local declarations
	// {{{
	wire			trace_xclk_valid, trace_xclk_ready,
				trace_xclk_last;
	wire	[IW-1:0]	trace_xclk_data;
	wire			xclk_fifo_full, xclk_fifo_empty;

	wire	[LGFRAME-1:0]	pix_width, pix_height, pix_half_height;
	wire			ign_tfr_valid, ign_tfr_ready;

	wire	trace_data_valid, wfall_data_valid,
		trace_data_ready, wfall_data_ready,
		trace_data_last, wfall_data_last;
	wire	[IW-1:0]	trace_data_data, wfall_data_data;

	wire			src_valid, src_ready, src_last, src_user;
	wire	[0:0]		src_data;

	wire			trace_valid, trace_ready, trace_last,
				trace_user;
	wire	[1:0]		trace_data;

	wire			top_valid, top_ready, top_last, top_user;
	wire	[1:0]		top_data;
	wire	[23:0]		top_color;

	wire			wfall_valid, wfall_ready, wfall_last,wfall_user;
	wire	[8-1:0]		wfall_data;

	wire	[7:0]		wfall_red, wfall_green, wfall_blue;
	wire	[23:0]		wfall_color;

	wire			top_err, bottom_err;

	reg	[LGFRAME-1:0]	half_height;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Send the signal to both IPs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	axisbroadcast #(
		.C_AXIS_DATA_WIDTH(IW+1), .NM(2), .LGFIFO(4)
	) u_stream_splitter (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIS_TVALID(S_AXIS_TVALID),
		.S_AXIS_TREADY(S_AXIS_TREADY),
		.S_AXIS_TDATA({ S_AXIS_TLAST, S_AXIS_TDATA }),
		//
		.M_AXIS_TVALID({ trace_xclk_valid, wfall_data_valid }),
		.M_AXIS_TREADY({ trace_xclk_ready, wfall_data_ready }),
		.M_AXIS_TDATA({ trace_xclk_last, trace_xclk_data,
					wfall_data_last, wfall_data_data })
		// }}}
	);

	// The trace will want it on the pixel clock, so cross clock domains
	afifo #(
		.WIDTH(IW+1)
	) u_trace_afifo (
		// {{{
		.i_wclk(i_clk), .i_wr_reset_n(!i_reset),
		.i_wr(trace_xclk_valid),
			.i_wr_data({ trace_xclk_last, trace_xclk_data }),
			.o_wr_full(xclk_fifo_full),
		.i_rclk(i_pixclk), .i_rd_reset_n(!i_pix_reset),
		.i_rd(trace_data_ready),
			.o_rd_data({ trace_data_last, trace_data_data }),
			.o_rd_empty(xclk_fifo_empty)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Start the video stream out with a blank stream
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	vid_empty #(
		// {{{
		.LGFRAME(LGFRAME), .PW(1), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF),
		.PIXEL(PIXEL)
		// }}}
	) u_empty (
		// {{{
		.i_clk(i_pixclk), .i_reset(i_pix_reset),
		//
		.i_width(pix_width), .i_height(pix_height),
		//
		.M_VID_VALID(src_valid), .M_VID_READY(src_ready),
			.M_VID_DATA( src_data),
			.M_VID_LAST( src_last), .M_VID_USER( src_user)
		// }}}
	);

	always @(posedge i_clk)
		half_height <= { 1'b0, i_height[LGFRAME-1:1] } - 1;

	tfrvalue #(
		.W(3*LGFRAME), .DEFAULT({ 16'd800, 16'd600, 16'd299 })
	) u_pixsize (
		// {{{
		.i_a_clk(i_clk), .i_a_reset_n(!i_reset),
		.i_a_valid(1'b1), .o_a_ready(ign_tfr_ready),
			.i_a_data({ i_width, i_height, half_height }),
		.i_b_clk(i_pixclk), .i_b_reset_n(!i_pix_reset),
		.o_b_valid(ign_tfr_valid), .i_b_ready(1'b1),
			.o_b_data({ pix_width, pix_height, pix_half_height })
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Add to that blank stream the spectrum trace
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	assign	trace_xclk_ready = !xclk_fifo_full;
	assign	trace_data_valid = !xclk_fifo_empty;

	vid_trace #(
		// {{{
		.LGFRAME(LGFRAME), .LGLEN(LGNFFT), .IW(IW), .PW(2),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF), .OPT_TRIGGER(0),
		.OPT_FRAMED(1'b1), .OPT_UNSIGNED(1'b1),
		.OPT_TRUNCATE_WIDTH(1'b1),
		.BACKGROUND_COLOR(2'b00), .AXIS_COLOR(2'b10),
		.LINE_COLOR(2'b11),
		.DEF_VSCALE({ 8'h1, {(LGFRAME-8){1'b0}} })
		// }}}
	) u_spectrogram (
		// {{{
		.S_AXI_ACLK(i_pixclk), .S_AXI_ARESETN(!i_pix_reset),
		//
		.i_trigger_en(1'b0), .i_trigger(1'b0), .i_trigger_reset(1'b1),
		//
		.i_width(pix_width), .i_height(pix_half_height),
		//
		.S_AXIS_TVALID(trace_data_valid),
		.S_AXIS_TREADY(trace_data_ready),
		.S_AXIS_TDATA( trace_data_data),
		.S_AXIS_TLAST( trace_data_last),
		//
		.M_VID_VALID(trace_valid),
		.M_VID_READY(trace_ready),
		.M_VID_DATA( trace_data),
		.M_VID_LAST( trace_last),
		.M_VID_USER( trace_user)
		// }}}
	);

	axisvoverlay #(
		// {{{
		.LGFRAME(LGFRAME), .ALPHA_BITS(0), .COLORS(1),
		.BITS_PER_PIXEL(2), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF),
		.OPT_LINE_BREAK(1'b1)
		// }}}
	) u_tophalf (
		// {{{
		.ACLK(i_pixclk), .ARESETN(!i_pix_reset),
		//
		.i_enable(1'b1), .i_hpos(0), .i_vpos(0), .o_err(top_err),
		//
		.S_PRI_TVALID(src_valid), .S_PRI_TREADY(src_ready),
			.S_PRI_TDATA({(2){src_data}}), .S_PRI_TLAST(src_last),
			.S_PRI_TUSER(src_user),
		//
		.S_OVW_TVALID(trace_valid), .S_OVW_TREADY(trace_ready),
			.S_OVW_TDATA(trace_data), .S_OVW_TLAST(trace_last),
			.S_OVW_TUSER(trace_user),
		//
		.M_VID_TVALID(top_valid), .M_VID_TREADY(top_ready),
			.M_VID_TDATA(top_data), .M_VID_TLAST(top_last),
			.M_VID_TUSER(top_user)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// And then add to that the raster on the bottom
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	vid_waterfall #(
		// {{{
		.LGFRAME(LGFRAME), .PW(8),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF), .AW(AW), .DW(DW)
		// }}}
	) u_waterfall (
		// {{{
		.i_pixclk(i_pixclk),
		//
		.i_baseaddr(i_baseaddr), .i_lastaddr(i_lastaddr),
		.i_width(i_width), .i_height(half_height),
		.i_en(i_en),
		//
		.S_AXIS_TVALID(wfall_data_valid),
			.S_AXIS_TREADY(wfall_data_ready),
			.S_AXIS_TDATA(wfall_data_data),
			.S_AXIS_TLAST(wfall_data_last),
		//
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.o_wb_cyc(o_wb_cyc), .o_wb_stb(o_wb_stb), .o_wb_we(o_wb_we),
			.o_wb_addr(o_wb_addr), .o_wb_data(o_wb_data),
			.o_wb_sel(o_wb_sel),
		.i_wb_stall(i_wb_stall), .i_wb_ack(i_wb_ack),
		.i_wb_data(i_wb_data), .i_wb_err(i_wb_err),
		//
		.M_VID_TVALID(wfall_valid),
		.M_VID_TREADY(wfall_ready),
		.M_VID_TDATA(wfall_data),
		.M_VID_TLAST(wfall_last),
		.M_VID_TUSER(wfall_user),
		//
		.o_debug(o_debug)
		// }}}
	);

	vid_clrmap
	u_clrmap (
		.i_pixel(wfall_data),
		.o_r(wfall_red),
		.o_g(wfall_green),
		.o_b(wfall_blue)
	);

	assign	wfall_color = { wfall_red, wfall_green, wfall_blue };
	assign	top_color = {(3){ top_data[1], {(7){top_data[0]}}  }};

	axisvoverlay #(
		// {{{
		.LGFRAME(LGFRAME), .ALPHA_BITS(0), .COLORS(3),
		.BITS_PER_PIXEL(8), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF),
		.OPT_LINE_BREAK(1'b1)
		// }}}
	) u_bottomhalf (
		// {{{
		.ACLK(i_pixclk), .ARESETN(!i_pix_reset),
		//
		.i_enable(1'b1), .i_hpos({(LGFRAME){1'b0}}),
			.i_vpos(pix_height/2+1), .o_err(bottom_err),
		//
		.S_PRI_TVALID(top_valid), .S_PRI_TREADY(top_ready),
			.S_PRI_TDATA(top_color), .S_PRI_TLAST(top_last),
			.S_PRI_TUSER(top_user),
		//
		.S_OVW_TVALID(wfall_valid), .S_OVW_TREADY(wfall_ready),
			.S_OVW_TDATA(wfall_color), .S_OVW_TLAST(wfall_last),
			.S_OVW_TUSER(wfall_user),
		//
		.M_VID_TVALID(M_VID_VALID), .M_VID_TREADY(M_VID_READY),
			.M_VID_TDATA(M_VID_DATA), .M_VID_TLAST(M_VID_LAST),
			.M_VID_TUSER(M_VID_USER)
		// }}}
	);

	// }}}

	assign	o_split_err = { (o_wb_cyc && i_wb_err), top_err, bottom_err };

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, top_err, bottom_err,
				ign_tfr_valid, ign_tfr_ready };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
