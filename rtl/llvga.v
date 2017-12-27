////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	llvga.v
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017, Gisselquist Technology, LLC
//
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
//
module	llvga(i_pixclk, i_reset, i_test,
		// External connections
		i_rgb_pix,
		// Video mode information
		i_hm_width,  i_hm_porch, i_hm_synch, i_hm_raw,
		i_vm_height, i_vm_porch, i_vm_synch, i_vm_raw,
		o_rd, o_newline, o_newframe,
		// VGA connections
		o_vsync, o_hsync, o_red, o_grn, o_blu);
	parameter	BITS_PER_COLOR = 4;
	localparam	BPC = BITS_PER_COLOR,
			BITS_PER_PIXEL = 3 * BPC,
			BPP = BITS_PER_PIXEL;
	input	wire			i_pixclk, i_reset, i_test;
	input	wire	[BPP-1:0]	i_rgb_pix;
	//
	input	wire	[11:0]		i_hm_width, i_hm_porch,
					i_hm_synch, i_hm_raw;
	input	wire	[11:0]		i_vm_height, i_vm_porch,
					i_vm_synch, i_vm_raw;
	// input	[3:0]	i_red, i_grn, i_blu;
	output	reg	o_rd, o_newline, o_newframe;
	output	reg	o_vsync, o_hsync;
	output	reg	[3:0]	o_red, o_grn, o_blu;


	wire	[BPC-1:0]	i_red, i_grn, i_blu;
	assign	i_red = i_rgb_pix[3*BPC-1:2*BPC];
	assign	i_grn = i_rgb_pix[2*BPC-1:  BPC];
	assign	i_blu = i_rgb_pix[  BPC-1:0];

	reg	[11:0]	hpos, vpos;
	reg		hrd, vrd;

	initial	hpos       = 12'h0;
	initial	o_newline  = 0;
	initial	o_hsync = 0;
	initial	hrd = 1;
	always @(posedge i_pixclk)
		if (i_reset)
		begin
			hpos <= 12'h0;
			o_newline <= 1'b0;
			o_hsync <= 1'b0;
			hrd <= 1;
		end else
		begin
			hrd <= (hpos < i_hm_width-12'd2)
					||(hpos >= i_hm_raw-12'd2);
			if (hpos < i_hm_raw-1'b1)
				hpos <= hpos + 1'b1;
			else
				hpos <= 0;
			o_newline <= (hpos == i_hm_width-12'd2);
			o_hsync <= (hpos >= i_hm_porch-1'b1)&&(hpos<i_hm_synch-1'b1);
		end

	always @(posedge i_pixclk)
	if (i_reset)
		o_newframe <= 1'b0;
	else if ((hpos == i_hm_width - 12'd2)&&(vpos == i_vm_height-12'd1))
		o_newframe <= 1'b1;
	else
		o_newframe <= 1'b0;

	initial	vpos = 12'h0;
	initial	o_vsync = 1'b0;
	always @(posedge i_pixclk)
		if (i_reset)
		begin
			vpos <= 12'h0;
			o_vsync <= 1'b0;
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
			o_vsync <= (vpos >= i_vm_porch-1'b1)&&(vpos<i_vm_synch-1'b1);
		end

	initial	vrd = 1'b1;
	always @(posedge i_pixclk)
		vrd <= (vpos < i_vm_height)&&(!i_reset);

	reg	first_frame;

	initial	first_frame = 1'b1;
	always @(posedge i_pixclk)
		if (i_reset)
			first_frame <= 1'b1;
		else if (o_newframe)
			first_frame <= 1'b0;

	wire	w_rd;
	assign	w_rd = (hrd)&&(vrd)&&(!first_frame);

	wire	[(BPC-1):0]	tst_red, tst_grn, tst_blu;

	vgatest	#(BPC)	vgatsrc(i_pixclk, i_reset,
				i_hm_width, i_vm_height,
				o_rd, o_newline, o_newframe,
				{ tst_red, tst_grn, tst_blu });

	initial	o_rd = 1'b0;
	always @(posedge i_pixclk)
		if (i_reset)
			o_rd <= 1'b0;
		else
			o_rd <= w_rd;

	always @(posedge i_pixclk)
		if (w_rd)
		begin
			o_red <= (i_test) ? tst_red : i_red;
			o_grn <= (i_test) ? tst_grn : i_grn;
			o_blu <= (i_test) ? tst_blu : i_blu;
		end else begin
			o_red <= 4'h0;
			o_grn <= 4'h0;
			o_blu <= 4'h0;
		end

//
// Formal properties for verification purposes
//
`ifdef	FORMAL
	reg	f_past_valid;
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

	wire	[47:0]	f_vmode, f_hmode;
	assign	f_hmode = { i_hm_width,  i_hm_porch, i_hm_synch, i_hm_raw };
	assign	f_vmode = { i_vm_height, i_vm_porch, i_vm_synch, i_vm_raw };

	reg	[47:0]	f_last_vmode, f_last_hmode;
	always @(posedge i_pixclk)
		f_last_vmode <= f_vmode;
	always @(posedge i_pixclk)
		f_last_hmode <= f_hmode;

	reg	f_stable_mode;
	always @(*)
		f_stable_mode <= (f_last_vmode == f_vmode)&&(f_last_hmode == f_hmode);

	always @(*)
		if (!i_reset)
			assume(f_stable_mode);

	always @(posedge i_pixclk)
	if ((f_past_valid)&&(!i_reset)&&(f_stable_mode)
			&&($past(f_stable_mode))
			&&($past(f_past_valid,2))&&($past(f_stable_mode,2))
			&&($past(f_past_valid,3))&&($past(f_stable_mode,3))
			)
	begin
		if ($past(i_reset))
		begin
			assert(hpos == 0);
			assert(vpos == 0);
		end else begin
			assert(hpos < i_hm_raw);
			assert(vpos < i_vm_raw);
		end

		if ((hpos < i_hm_width)&&(vpos < i_vm_height)
				&&(!first_frame))
			assert(o_rd);

		if (hpos < i_hm_porch)
			assert(!o_hsync);
		else if (hpos < i_hm_synch)
			assert(o_hsync);
		else
			assert(!o_hsync);

		if (vpos < i_vm_porch)
			assert(!o_vsync);
		else if (vpos < i_vm_synch)
			assert(o_vsync);
		else
			assert(!o_vsync);

		if (hpos == i_hm_width-1'b1)
			assert(o_newline);
		else
			assert(!o_newline);

		if ((vpos == i_vm_height-1'b1)&&(o_newline))
			assert(o_newframe);
		else
			assert(!o_newframe);


	end
`endif
endmodule

