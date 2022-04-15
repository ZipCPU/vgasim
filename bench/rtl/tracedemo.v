////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	tracedemo.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Demonstrates using the modules within the design how an
//		x vs time plot can be drawn on an HDMI output.
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
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
// `define	HDMI
// }}}
module	tracedemo #(
		// {{{
		// Verilator lint_off UNUSED
		localparam	OPT_TUSER_IS_SOF = 1'b1
		// Verilator lint_on  UNUSED
		// }}}
	) (
		// {{{
		input	wire	i_clk,
		input	wire	i_reset,
		// Pixel/video outputs
		// {{{
		output	wire	[9:0]	o_hdmi_red,
		output	wire	[9:0]	o_hdmi_grn,
		output	wire	[9:0]	o_hdmi_blu
		// }}}
		// }}}
	);

	// Register/net declarations
	// {{{
	localparam			LGFRAME = 11;

	localparam	[LGFRAME-1:0]	DEF_WIDTH  = 1280;
	localparam	[LGFRAME-1:0]	DEF_HPORCH = 1328;
	localparam	[LGFRAME-1:0]	DEF_HSYNC  = 1440;
	localparam	[LGFRAME-1:0]	DEF_HRAW   = 1688;
		//
	localparam	[LGFRAME-1:0]	DEF_HEIGHT = 1024;
	localparam	[LGFRAME-1:0]	DEF_VPORCH = 1025;
	localparam	[LGFRAME-1:0]	DEF_VSYNC  = 1028;
	localparam	[LGFRAME-1:0]	DEF_VRAW   = 1066;

	localparam	LGDEC = 9;
	localparam [0:0]	TEST_FRAMING = 1;
	localparam [0:0]	TEST_UNSIGNED = 0;

	localparam	IW = 13;	// Fixed by the sin_table routine
	reg	[16:0]	phase;
	wire		s_aux;
	// Verilator lint_off UNUSED
	wire	signed	[IW-1:0]	as_val;
	reg	signed	[IW-1:0]	s_val;
	// Verilator lint_on  UNUSED


	wire		vtrace_valid, vtrace_ready, vtrace_hlast, vtrace_vlast;
	wire	[23:0]	vtrace_data;
	wire		hdmi_empty, vtrace_full;
	wire	[4:0]	vtrace_fill;

	reg			decimation_stb;
	reg	[LGDEC-1:0]	decimation_counter;

	reg	[IW-1:0]	last_sample;
	reg			frame_last, dir;

	wire		trace_ready;
	wire		hdmi_valid, hdmi_ready, hdmi_hlast, hdmi_vlast;
	wire	[23:0]	hdmi_data;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate a sine wave signal
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// We need something to test with and demo, so we'll build that signal
	// here.  It's a basic sinewave.
	//

	initial	phase = 0;
	always @(posedge i_clk)
		phase <= phase + 1;

	//
	// The sintable IP comes from my CORDIC project:
	//	https://github.com/ZipCPU/cordic
	// It's just a simple table lookup.
	//

	sintable
	u_sin (
		.i_clk(i_clk), .i_reset(i_reset), .i_ce(1'b1),
		.i_phase( phase), .o_val(as_val),
		.i_aux(1'b0), .o_aux(s_aux)
	);

	always @(*)
	if (TEST_UNSIGNED)
	begin
		s_val = ((as_val[12]) ? (-as_val) : as_val) >> 1;
	end else
		s_val = as_val;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The trace video generator
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Here we turn our sinewave signal input into a video signal output.
	//

	// Decimation
	// {{{
	// First problem: at the full sample rate, the rate's really way to
	// high -- especially if we want to test the overlap capability of the
	// IP.  Therefore, let's reduce the rate a bit.
	initial	decimation_counter = 0;
	always @(posedge i_clk)
	if (i_reset)
		{ decimation_stb, decimation_counter } <= 0;
	else
		{ decimation_stb, decimation_counter } <= decimation_counter+ 1;
	// }}}

	// Framing
	// {{{
	// If we want to test the framing capability of the IP, we need to
	// generate a framing signal.  Let's use one of two signals to sync
	// on here:
	//
	//	UNSIGNED
	//		Capture the low inflection point, where the sine
	//		would've gone through zero if it hadn't been (absolute
	//		valued)
	//	!UNSIGNED
	//		Capture the rising edge as a starting point
	//
	always @(posedge i_clk)
	if (decimation_stb)
		last_sample <= s_val;

	always @(posedge i_clk)
	if (decimation_stb)
	begin
		dir <= (last_sample >= s_val); // Direction
		if (TEST_UNSIGNED)
		begin
			frame_last <= dir && (last_sample < s_val);
		end else
			frame_last <= last_sample[IW-1] && !s_val[IW-1];
	end
	// }}}

	vid_trace #(
		// {{{
		.PW(24), .LGLEN(LGFRAME-1), .IW(IW),
		.HEXTRA(6),
		.BACKGROUND_COLOR(24'h000000),
		.AXIS_COLOR(24'h38ff38),
		.LINE_COLOR(24'hffffff),
		.LGFRAME(LGFRAME),
		.OPT_TUSER_IS_SOF(1'b0),
		.OPT_TRIGGER(1'b1),
		.OPT_FRAMED(TEST_FRAMING),
		.OPT_UNSIGNED(TEST_UNSIGNED)
		// }}}
	) u_trace (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.i_trigger_en(1'b0), .i_trigger(1'b0), .i_trigger_reset(1'b0),
		//
		.S_AXIS_TVALID(decimation_stb), .S_AXIS_TREADY(trace_ready),
		.S_AXIS_TDATA(s_val), .S_AXIS_TLAST(frame_last),
		//
		.M_VID_VALID(vtrace_valid), .M_VID_READY(vtrace_ready),
		.M_VID_DATA(vtrace_data), .M_VID_LAST(vtrace_vlast),
		.M_VID_USER(vtrace_hlast),
		//
		.i_width(DEF_WIDTH), .i_height(DEF_HEIGHT)
		// }}}
	);

	// A quick synchronous FIFO
	sfifo #(
		// {{{
		.BW(24+2), .LGFLEN(4)
		// }}}
	) trace_fifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wr(vtrace_valid),
			.i_data({ vtrace_hlast, vtrace_vlast, vtrace_data }),
			.o_full(vtrace_full), .o_fill(vtrace_fill),
		.i_rd(hdmi_ready),
			.o_data({ hdmi_hlast, hdmi_vlast, hdmi_data }),
			.o_empty(hdmi_empty)
		// }}}
	);

	assign	hdmi_valid = !hdmi_empty;
	assign	vtrace_ready = !vtrace_full;

	// Verilator lint_off UNUSED
	wire	vtrace_unused;
	assign	vtrace_unused = &{ 1'b0, vtrace_fill };
	// Verilator lint_on  UNUSED

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Video to HDMI converter
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Last step: convert the AXI-stream video signal output into HDMI.
	// Some subtleties: I'm not using TLAST and TUSER, but instead HLAST
	// and VLAST.  In Xilinx land, HLAST is the same as TLAST, and TUSER
	// would be set on the clock following HLAST && VLAST.  It's a
	// subtlely different protocol, although an annoying one to swap
	// between.  (VLAST && HLAST is easier to sync to ...)
	//

	axishdmi #(
		// {{{
		.HW(LGFRAME), .VW(LGFRAME)
		// }}}
	) u_hdmi (
		// {{{
		.i_pixclk(i_clk),
		.i_reset(i_reset),
		// Incoming video stream
		.i_valid(hdmi_valid),
		.o_ready(hdmi_ready),
		.i_hlast(hdmi_hlast),
		.i_vlast(hdmi_vlast),
		.i_rgb_pix(hdmi_data),
		//
		.i_hm_width(DEF_WIDTH),
		.i_hm_porch(DEF_HPORCH),
		.i_hm_synch(DEF_HSYNC),
		.i_hm_raw(DEF_HRAW),
		//
		.i_vm_height(DEF_HEIGHT),
		.i_vm_porch(DEF_VPORCH),
		.i_vm_synch(DEF_VSYNC),
		.i_vm_raw(DEF_VRAW),
		//
		.o_red(o_hdmi_red),
		.o_grn(o_hdmi_grn),
		.o_blu(o_hdmi_blu)
		// }}}
	);
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, trace_ready, s_val[2:0], s_aux,
				last_sample };
	// verilator lint_on  UNUSED
	// }}}
endmodule
