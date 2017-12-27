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
		o_vga_vsync, o_vga_hsync, o_vga_red, o_vga_grn, o_vga_blu);
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
	output	reg	o_vga_vsync, o_vga_hsync;
	output	reg	[3:0]	o_vga_red, o_vga_grn, o_vga_blu;


	wire	[BPC-1:0]	i_red, i_grn, i_blu;
	assign	i_red = i_rgb_pix[3*BPC-1:2*BPC];
	assign	i_grn = i_rgb_pix[2*BPC-1:  BPC];
	assign	i_blu = i_rgb_pix[  BPC-1:0];

	reg	[11:0]	hpos, vpos;
	reg		hrd, vrd;

	always @(posedge i_pixclk)
		if (i_reset)
		begin
			hpos <= 12'h00;
			o_newline <= 1'b0;
			o_vga_hsync <= 1'b0;
		end else
		begin
			hrd <= (hpos < i_hm_width-12'd2)
					||(hpos >= i_hm_raw-12'd2);
			if (hpos < i_hm_raw-1'b1)
				hpos <= hpos + 1'b1;
			else
				hpos <= 0;
			o_newline <= (hpos == i_hm_width);
			o_vga_hsync <= (hpos >= i_hm_porch)&&(hpos<i_hm_synch);
		end

	always @(posedge i_pixclk)
		if (i_reset)
		begin
			vpos <= 12'h00;
			o_newframe <= 1'b0;
			o_vga_vsync <= 1'b0;
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
			o_newframe  <= (vpos == i_vm_height-1'b1);
			o_vga_vsync <= (vpos >= i_vm_porch-1'b1)&&(vpos<i_vm_synch-1'b1);
		end else
			o_newframe <= 1'b0;

	always @(posedge i_pixclk)
		vrd <= (vpos < i_vm_height)&&(!i_reset);

	wire	w_rd;
	assign	w_rd = (hrd)&&(vrd);

	wire	[(BPC-1):0]	tst_red, tst_grn, tst_blu;

	vgatest	#(BPC)	vgatsrc(i_pixclk, i_reset,
				i_hm_width, i_vm_height,
				o_rd, o_newline, o_newframe,
				{ tst_red, tst_grn, tst_blu });

	always @(posedge i_pixclk)
		if (w_rd)
		begin
			o_rd <= 1'b1;
			o_vga_red <= (i_test) ? tst_red : i_red;
			o_vga_grn <= (i_test) ? tst_grn : i_grn;
			o_vga_blu <= (i_test) ? tst_blu : i_blu;
		end else begin
			o_rd <= 1'b0;
			o_vga_red <= 4'h0;
			o_vga_grn <= 4'h0;
			o_vga_blu <= 4'h0;
		end
endmodule

