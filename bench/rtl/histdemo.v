////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	histdemo.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Demonstrates using the modules within the design how a
//		histogram can be drawn on an HDMI output.
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
module	histdemo #(
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

	reg	[12:0]	phase;
	wire		s_aux;

	wire		hist_ready;
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

	// Verilator lint_off UNUSED
	wire	signed	[12:0]	as_val;
	reg	signed	[12:0]	s_val, tmp_val;
	// Verilator lint_on  UNUSED

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
		.i_phase({ phase, 4'h0 }), .o_val(as_val),
		.i_aux(1'b0), .o_aux(s_aux)
	);

	always @(*)
	begin
		// Some quick (no-so-synthesizable) data manipulations
		// Just to know we're doing this right ...
		//
		// Divide by four to give us headroom
		tmp_val = { {(2){as_val[12]}}, as_val[12:2] };
		//
		// Multiply by three--so we don't use the full range
		//   (Full range is okay to use, I just want to make
		//    sure zero inputs to the histogram produce zero
		//    outputs here.)
		s_val = tmp_val * 3;
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The histogram video generator
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Here we turn our sinewave signal input into a video signal output.
	//

	vid_histogram #(
		// {{{
		.LGHIST(14), .PW(24),
		.ACTIVE_PIXEL(24'h00ff00),
		.BACKGROUND_PIXEL(24'h000000),
		.LINE_PIXEL(24'h0000ff),
		.LGDIM(LGFRAME), .IW(10),
		.OPT_TUSER_IS_SOF(1'b0)
		// }}}
	) u_histogram (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIS_TVALID(1'b1), .S_AXIS_TREADY(hist_ready),
		.S_AXIS_TDATA(s_val[12:3]),
		//
		.M_VID_VALID(hdmi_valid), .M_VID_READY(hdmi_ready),
		.M_VID_DATA(hdmi_data), .M_VID_LAST(hdmi_vlast),
		.M_VID_USER(hdmi_hlast),
		//
		.i_width(DEF_WIDTH), .i_height(DEF_HEIGHT)
		// }}}
	);

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
	assign	unused = &{ 1'b0, hist_ready, s_val[2:0], s_aux };
	// verilator lint_on  UNUSED
	// }}}
endmodule
