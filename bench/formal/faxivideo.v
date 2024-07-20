////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxivideo.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022, Gisselquist Technology, LLC
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
module	faxivideo #(
		// {{{
		parameter	PW = 24,		// Pixel width
		parameter	LGDIM = 10,
		parameter [0:0]	OPT_TUSER_IS_SOF = 1,
		// Camera sources can't handle backpressure
		parameter [0:0]	OPT_SOURCE = 0
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset_n,
		input	wire		S_VID_TVALID,
		input	wire		S_VID_TREADY,
		input	wire [PW-1:0]	S_VID_TDATA,
		input	wire		S_VID_TLAST,
		input	wire		S_VID_TUSER,
		//
		input	wire [LGDIM-1:0]	i_width, i_height,
		output	reg	[LGDIM-1:0]	o_xpos, o_ypos,
		output	reg			f_known_height,
		output	wire			o_hlast, o_vlast, o_sof
		// }}}
	);

	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!i_reset_n);

	// Stability
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || !i_reset_n)
	begin end else if ($past(!i_reset_n))
	begin
		assert(!S_VID_TVALID);
	end else if (!OPT_SOURCE && $past(S_VID_TVALID && !S_VID_TREADY))
	begin
		assert(S_VID_TVALID);
		assert($stable(S_VID_TDATA));
		assert($stable(S_VID_TLAST));
		assert($stable(S_VID_TUSER));
	end
	// }}}

	// Calculate X & Y positions
	// {{{
	initial	o_xpos = 0;
	initial	o_ypos = 0;
	initial	f_known_height = 0;
	always @(posedge i_clk)
	if (!i_reset_n)
	begin
		o_xpos <= 0;
		o_ypos <= 0;
		f_known_height <= 0;
	end else if (S_VID_TVALID && (OPT_SOURCE || S_VID_TREADY))
	begin
		if (o_xpos + 1 == i_width)
			o_xpos <= 0;
		else
			o_xpos <= o_xpos + 1;

		if (o_xpos + 1 == i_width)
		begin
			if (o_ypos + 1 == i_height)
			begin
				o_ypos <= 0;
				f_known_height <= 1;
			end else
				o_ypos <= o_ypos + 1;
		end
	end
	// }}}

	assign	o_hlast = (o_xpos == i_width  - 1);
	assign	o_vlast = (o_ypos == i_height - 1);
	assign	o_sof   = (o_xpos == 0 && o_ypos == 0);

	// Height/Width assumptions
	// {{{
	always @(posedge i_clk)
	if (f_past_valid && $past(i_reset_n) && i_reset_n)
	begin
		assume($stable(i_width));
		assume($stable(i_height));

		if (!o_sof || S_VID_TVALID)
		begin
			assume(i_width  > 2);
			assume(i_height > 2);
		end
	end
	// }}}

	always @(posedge i_clk)
	if (f_past_valid && $past(i_reset_n) && i_reset_n)
	begin
		assert(o_xpos < i_width);
		assert(o_ypos < i_height);
	end

	always @(posedge i_clk)
	if (f_past_valid && i_reset_n && $past(i_reset_n) && S_VID_TVALID)
	begin
		if (OPT_TUSER_IS_SOF)
		begin
			assert(S_VID_TLAST == o_hlast);
			assert(!f_known_height || S_VID_TUSER == o_sof);
		end else begin
			assert(S_VID_TLAST == (o_vlast && o_hlast));
			assert(S_VID_TUSER == o_hlast);
		end
	end

endmodule
