////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axisvga.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Converts an AXI-stream pixel stream (with framing information)
//		into a VGA signal with appropriate SYNC signals.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2017-2022, Gisselquist Technology, LLC
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
// }}}
module	axisvga #(
		// {{{
		parameter	HW=12,
				VW=12,
		// HDMI *only* works with 24-bit color, using 8-bits per color
		localparam	BITS_PER_COLOR = 8,
		localparam	BPC = BITS_PER_COLOR,
				BITS_PER_PIXEL = 3 * BPC,
				BPP = BITS_PER_PIXEL
		// }}}
	) (
		// {{{
		input	wire	i_pixclk,
		// Verilator lint_off SYNCASYNCNET
		input	wire			i_reset,
		// Verilator lint_on SYNCASYNCNET
		//
		// AXI Stream interface
		// {{{
		input	wire		i_valid,
		output	reg		o_ready,
		input	wire		i_hlast,
		input	wire		i_vlast,
		input	wire [BPP-1:0]	i_rgb_pix,
		// }}}
		//
		// Video mode information
		// {{{
		input	wire [HW-1:0]	i_hm_width,
		input	wire [HW-1:0]	i_hm_porch,
		input	wire [HW-1:0]	i_hm_synch,
		input	wire [HW-1:0]	i_hm_raw,
		//
		input	wire [VW-1:0]	i_vm_height,
		input	wire [VW-1:0]	i_vm_porch,
		input	wire [VW-1:0]	i_vm_synch,
		input	wire [VW-1:0]	i_vm_raw,
		// }}}
		//
		// VGA connections
		output	reg		o_vsync,
		output	reg		o_hsync,
		output	reg	[7:0]	o_red,
		output	reg	[7:0]	o_grn,
		output	reg	[7:0]	o_blu
		// }}}
	);

	// Local declarations
	// {{{
	reg	pix_reset, pix_reset_pipe;
	reg	r_newline, r_newframe, lost_sync;

	wire	[BPC-1:0]	i_red, i_grn, i_blu;

	reg	[HW-1:0]	hpos;
	reg	[VW-1:0]	vpos;
	reg			hrd, vrd;
	reg			first_frame;
	wire			w_rd;

	assign	i_red = i_rgb_pix[3*BPC-1:2*BPC];
	assign	i_grn = i_rgb_pix[2*BPC-1:  BPC];
	assign	i_blu = i_rgb_pix[  BPC-1:0];
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchronize the reset release
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	{ pix_reset, pix_reset_pipe } = -1;
	always @(posedge i_pixclk, posedge i_reset)
	if (i_reset)
		{ pix_reset, pix_reset_pipe } <= -1;
	else
		{ pix_reset, pix_reset_pipe } <= { pix_reset_pipe, 1'b0 };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Handle horizontal timing and synchronization
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// hpos, r_newline, o_sync, hrd
	// {{{
	initial	hpos       = 0;
	initial	r_newline  = 0;
	initial	o_hsync = 1;
	initial	hrd = 1;
	always @(posedge i_pixclk)
	if (pix_reset)
	begin
		// {{{
		hpos <= 0;
		r_newline <= 1'b0;
		o_hsync <= 1'b1;
		hrd <= 1;
		// }}}
	end else begin
		// {{{
		hrd <= (hpos < i_hm_width-2)
				||(hpos >= i_hm_raw-2);
		if (hpos < i_hm_raw-1'b1)
			hpos <= hpos + 1'b1;
		else
			hpos <= 0;
		r_newline <= (hpos == i_hm_width-3);
		o_hsync <= (hpos < i_hm_porch-1'b1)||(hpos>=i_hm_synch-1'b1);
		// }}}
	end
	// }}}

	// lost_sync detection
	// {{{
	initial	lost_sync = 1;
	always @(posedge i_pixclk)
	if (pix_reset)
		lost_sync <= 1;
	else if (w_rd)
	begin
		if (r_newframe && i_hlast && i_vlast && i_valid)
			lost_sync <= 0;
		else begin
			if (!i_valid)
				lost_sync <= 1;
			if (i_hlast != r_newline)
				lost_sync <= 1;
			if ((i_vlast && i_hlast) != r_newframe)
				lost_sync <= 1;
		end
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Vertical / frame based timing and synchronization
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// r_newframe
	// {{{
	initial	r_newframe = 0;
	always @(posedge i_pixclk)
	if (pix_reset)
		r_newframe <= 1'b0;
	else if ((hpos == i_hm_width - 3)&&(vpos == i_vm_height-1))
		r_newframe <= 1'b1;
	else
		r_newframe <= 1'b0;
	// }}}

	// vpos, o_vsync
	// {{{
	initial	vpos = 0;
	initial	o_vsync = 1'b1;
	always @(posedge i_pixclk)
	if (pix_reset)
	begin
		vpos <= 0;
		o_vsync <= 1'b1;
	end else if (hpos == i_hm_porch-1'b1)
	begin
		if (vpos < i_vm_raw-1'b1)
			vpos <= vpos + 1'b1;
		else
			vpos <= 0;
		// Realistically, the new frame begins at the top
		// of the next frame.  Here, we define it as the end
		// last valid row.  That gives any software depending
		// upon this the entire time of the front and back
		// porches, together with the synch pulse width time,
		// to prepare to actually draw on this new frame before
		// the first pixel clock is valid.
		o_vsync <= (vpos < i_vm_porch-1'b1)||(vpos>=i_vm_synch-1'b1);
	end
	// }}}

	// vrd
	// {{{
	initial	vrd = 1'b1;
	always @(posedge i_pixclk)
		vrd <= (vpos < i_vm_height)&&(!pix_reset);
	// }}}

	// first_frame
	// {{{
	initial	first_frame = 1'b1;
	always @(posedge i_pixclk)
	if (pix_reset)
		first_frame <= 1'b1;
	else if (r_newframe)
		first_frame <= 1'b0;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-stream Ready generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// This really needs a skid buffer to be properly AXI stream compliant
	//

	// w_rd -- true if we are reading a pixel
	// {{{
	assign	w_rd = (hrd)&&(vrd)&&(!first_frame);
	// }}}

	// o_ready -- Incoming AXI stream signal, indicating we are ready to
	// receive a pixel
	// {{{
	always @(*)
	if (lost_sync)
		o_ready = (!i_vlast || !i_hlast) || (r_newframe && w_rd);
	else
		o_ready = w_rd;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing pixel generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_pixclk)
	if (w_rd)
	begin
		if (lost_sync)
		begin
			o_red <= 0;
			o_grn <= 0;
			o_blu <= 0;
		end else begin
			o_red <= i_red;
			o_grn <= i_grn;
			o_blu <= i_blu;
		end
	end else begin
		o_red <= 0;
		o_grn <= 0;
		o_blu <= 0;
	end
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties for verification purposes
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg		f_past_valid;
	wire	[47:0]	f_vmode, f_hmode;
	reg	[47:0]	f_last_vmode, f_last_hmode;
	reg		f_stable_mode;

	initial	f_past_valid = 1'b0;
	always @(posedge i_pixclk)
		f_past_valid <= 1'b1;
	always @(*)
		if (!f_past_valid)
			assume(i_reset);

	always @(*)
	begin
		assume(12'h10 < i_hm_width);
		assume(i_hm_width < i_hm_porch);
		assume(i_hm_porch < i_hm_synch);
		assume(i_hm_synch < i_hm_raw);

		assume(12'h10 < i_vm_height);
		assume(i_vm_height < i_vm_porch);
		assume(i_vm_porch  < i_vm_synch);
		assume(i_vm_synch  < i_vm_raw);
	end

	assign	f_hmode = { i_hm_width,  i_hm_porch, i_hm_synch, i_hm_raw };
	assign	f_vmode = { i_vm_height, i_vm_porch, i_vm_synch, i_vm_raw };

	always @(posedge i_pixclk)
		f_last_vmode <= f_vmode;
	always @(posedge i_pixclk)
		f_last_hmode <= f_hmode;

	always @(*)
		f_stable_mode = (f_last_vmode == f_vmode)&&(f_last_hmode == f_hmode);

	always @(*)
	if (!i_reset)
		assume(f_stable_mode);

	always @(posedge i_pixclk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(hpos == 0);
		assert(vpos == 0);
	end

	always @(posedge i_pixclk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!i_reset)
			&&(f_stable_mode)&&($past(f_stable_mode)))
	begin

		// The horizontal position counter should increment
		if ($past(hpos >= i_hm_raw-1'b1))
			assert(hpos == 0);
		else
			assert(hpos == $past(hpos)+1'b1);

		// The vertical position counter should increment
		if (hpos == i_hm_porch)
		begin
			if ($past(vpos >= i_vm_raw-1'b1))
				assert(vpos == 0);
			else
				assert(vpos == $past(vpos)+1'b1);
		end else
			assert(vpos == $past(vpos));

		// For induction purposes, we need to insist that both
		// horizontal and vertical counters stay within their
		// required ranges
		assert(hpos < i_hm_raw);
		assert(vpos < i_vm_raw);

		// If we are less than the data width for both horizontal
		// and vertical, then we should be asserting we are in a
		// valid data cycle
		// if ((hpos < i_hm_width)&&(vpos < i_vm_height)
				// &&(!first_frame))
			// assert(o_rd);

		//
		// The horizontal sync should only be valid between positions
		// i_hm_porch <= hpos < i_hm_sync, invalid at all other times
		//
		if (hpos < i_hm_porch)
			assert(o_hsync);
		else if (hpos < i_hm_synch)
			assert(!o_hsync);
		else
			assert(o_hsync);

		// Same thing for vertical
		if (vpos < i_vm_porch)
			assert(o_vsync);
		else if (vpos < i_vm_synch)
			assert(!o_vsync);
		else
			assert(o_vsync);

		// At the end of every horizontal line cycle, we assert
		// a new line
		if (hpos == i_hm_width-2)
			assert(r_newline);
		else
			assert(!r_newline);

		// At the end of every vertical frame cycle, we assert
		// a new frame, but only on the newline measure
		if ((vpos == i_vm_height-1'b1)&&(r_newline))
			assert(r_newframe);
		else
			assert(!r_newframe);
	end
`endif
// }}}
endmodule

