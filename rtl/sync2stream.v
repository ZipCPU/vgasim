////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sync2stream.v
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
// Copyright (C) 2020, Gisselquist Technology, LLC
//
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
module	sync2stream #(
		parameter [0:0]	OPT_INVERT_HSYNC = 1,
		parameter [0:0]	OPT_INVERT_VSYNC = 1
	) (
		input	wire				i_clk,
		input	wire				i_reset,
		//
		input	wire				i_pix_valid,
		input	wire				i_hsync,
		input	wire				i_vsync,
		input	wire	[24-1:0]		i_pixel,
		//
		output	reg				M_AXIS_TVALID,
		input	wire				M_AXIS_TREADY,
		output	reg	[24-1:0]		M_AXIS_TDATA,	// Color
		output	reg				M_AXIS_TLAST,	// Vsync
		output	reg				M_AXIS_TUSER,	// Hsync
		//
		output	reg	[15:0]			o_width,
		output	reg	[15:0]			o_hfront,
		output	reg	[15:0]			o_hsync,
		output	reg	[15:0]			o_raw_width,
		//
		output	reg	[15:0]			o_height,
		output	reg	[15:0]			o_vfront,
		output	reg	[15:0]			o_vsync,
		output	reg	[15:0]			o_raw_height,
		//
		output	reg				o_locked
	);

	wire		new_data_row, hsync, vsync;
	reg	[16:0]	hcount_pix, hcount_shelf, hcount_sync, hcount_tot;
	reg		hin_shelf, last_pv, hlocked;

	reg	linestart, has_pixels, has_vsync, newframe, last_hs,
		this_line_had_vsync, this_line_had_pixels, last_line_had_pixels;

	reg	[16:0]	vcount_lines, vcount_shelf, vcount_sync, vcount_tot;
	reg		vin_shelf, vlost_lock, vlocked;


	assign	hsync = OPT_INVERT_HSYNC ^ i_hsync;
	assign	vsync = OPT_INVERT_VSYNC ^ i_vsync;

	initial	last_pv = 0;
	always @(posedge i_clk)
		last_pv <= i_pix_valid;

	assign	new_data_row = (!last_pv)&&(i_pix_valid);


	initial	hcount_pix   = 0;
	initial	hcount_shelf = 0;
	initial	hcount_sync  = 0;
	initial	hcount_tot   = 0;
	initial	hin_shelf     = 1'b1;
	always @(posedge i_clk)
	if (new_data_row)
	begin
		hcount_pix   <= 0;
		hcount_shelf <= 0;
		hcount_sync  <= 0;
		hcount_tot   <= 0;
		hin_shelf    <= 1'b1;
	end else begin
		if (!hcount_tot[16])
			hcount_tot <= hcount_tot + 1'b1;
		if ((!hcount_pix[16])&&(i_pix_valid))
			hcount_pix <= hcount_pix + 1'b1;
		if ((!hcount_sync[16])&&(hsync))
			hcount_sync <= hcount_sync + 1'b1;
		if ((!hcount_shelf[16])&&(!i_pix_valid)
				&&(!hsync)&&(hin_shelf))
			hcount_shelf <= hcount_shelf + 1'b1;
		if (hsync)
			hin_shelf <= 1'b0;
	end

	always @(posedge i_clk)
		M_AXIS_TUSER <= !i_reset && i_pix_valid && (hcount_pix == o_width-1);

	initial	o_width     = 0;
	initial	o_raw_width = 0;
	initial	o_hfront    = 0;
	initial	o_hsync     = 0;
	always @(posedge i_clk)
	if (new_data_row)
	begin
		o_width     <= hcount_pix[15:0]; // -16'd10;
		o_raw_width <= hcount_tot[15:0]; // +16'd1;
		o_hfront    <= hcount_pix[15:0] + hcount_shelf[15:0]; // + 16'd11;
		o_hsync     <= hcount_pix[15:0] + hcount_shelf[15:0] + hcount_sync[15:0];
	end

	always @(posedge i_clk)
	begin
		if (new_data_row)
		begin
			hlocked <= 1;
			if ({ 1'b0, o_width } != hcount_pix)
				hlocked <= 0;
			if ({ 1'b0, o_raw_width } != hcount_tot)
				hlocked <= 0;
		end

		if (i_reset)
			hlocked <= 0;
	end


	initial	last_hs = 1'b0;
	always @(posedge i_clk)
		last_hs <= hsync;

	initial	linestart  = 1'b0;
	initial	has_pixels = 1'b0;
	initial	has_vsync  = 1'b0;
	initial	newframe   = 1'b0;
	always @(posedge i_clk)
	if ((!last_hs)&&(hsync))
	begin
		linestart  <= 1'b1;
		has_pixels <= 1'b0;
		has_vsync  <= 1'b0;
		this_line_had_vsync  <= has_vsync;
		this_line_had_pixels <= has_pixels;
		last_line_had_pixels <= last_line_had_pixels;
		newframe <= (has_pixels)&&(!this_line_had_pixels);
	end else begin
		linestart  <= 1'b0;
		newframe   <= 1'b0;
		if (i_pix_valid)
			has_pixels <= 1'b1;
		if (vsync)
			has_vsync  <= 1'b1;
	end

	initial	vcount_lines = 0;
	initial	vcount_shelf = 0;
	initial	vcount_sync  = 0;
	initial	vcount_tot   = 0;
	initial	vlost_lock   = 1;
	always @(posedge i_clk)
	if (linestart)
	begin
		if (newframe)
		begin
			vcount_lines <= 0;
			vcount_shelf <= 0;
			vcount_sync  <= 0;
			vcount_tot   <= 0;
			vin_shelf    <= 1'b1;
			vlost_lock   <= !hlocked;
		end else begin
			if (!vcount_tot[16])
				vcount_tot <= vcount_tot + 1'b1;
			if ((!vcount_lines[16])&&(this_line_had_pixels))
				vcount_lines <= vcount_lines + 1'b1;
			if ((!vcount_sync[16])&&(this_line_had_vsync))
				vcount_sync <= vcount_sync + 1'b1;
			if ((!vcount_shelf[16])&&(!this_line_had_pixels)
					&&(!this_line_had_vsync)&&(vin_shelf))
				vcount_shelf <= vcount_shelf + 1'b1;
			if (this_line_had_vsync)
				vin_shelf <= 1'b0;
			if (!hlocked)
				vlost_lock <= 1;
		end
	end

	always @(posedge i_clk)
		M_AXIS_TLAST <= !i_reset && i_pix_valid
			&& (hcount_pix == o_width-1)
			&& (vcount_lines == o_height-1);

	initial	o_height    = 0;
	initial	o_raw_height= 0;
	initial	o_vfront    = 0;
	initial	o_vsync     = 0;
	always @(posedge i_clk)
	if (newframe)
	begin
		o_height     <= vcount_lines[15:0] + 1'b1;
		o_raw_height <= vcount_tot[15:0] + 1'b1;
		o_vfront     <= vcount_shelf[15:0] + vcount_lines[15:0];
		o_vsync      <= vcount_sync[15:0] + vcount_shelf[15:0] + vcount_lines[15:0];
	end

	initial	vlocked = 0;
	always @(posedge i_clk)
	begin
		if (newframe)
		begin
			vlocked <= !vlost_lock && !vcount_tot[16];
			if ({ 1'b0, o_height } != vcount_lines + 1)
				vlocked <= 0;
			if ({ 1'b0, o_raw_height } != vcount_tot + 1)
				vlocked <= 0;
		end

		if (!hlocked)
			vlocked <= 0;
		if (i_reset)
			vlocked <= 0;
	end

	always @(*)
		o_locked = vlocked;

	always @(posedge i_clk)
		M_AXIS_TVALID <= i_pix_valid;

	always @(posedge i_clk)
		M_AXIS_TDATA <= i_pixel;

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_AXIS_TREADY };
	// Verilator lint_on  UNUSED
endmodule
