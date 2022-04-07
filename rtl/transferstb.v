////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	transferstb.v
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
// Copyright (C) 2015-2022, Gisselquist Technology, LLC
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
module	transferstb(i_src_clk, i_dest_clk, i_stb, o_stb);
	parameter	NFF=2;
	input	wire	i_src_clk, i_dest_clk, i_stb;
	output	reg	o_stb;

	// Generate a sticky flip-flop
	reg	lcl_stb, lcl_ack;
	initial	lcl_stb = 1'b0;
	always @(posedge i_src_clk)
		if (i_stb)
			lcl_stb <= 1'b1;
		else if (lcl_ack)
			lcl_stb <= 1'b0;

	// Transfer this sticky flip-flop
	reg	[NFF:0]	tfr_stb;
	initial	tfr_stb = 0;
	always @(posedge i_dest_clk)
		tfr_stb <= { tfr_stb[(NFF-1):0], lcl_stb };

	initial	o_stb = 1'b0;
	always @(posedge i_dest_clk)
		o_stb <= (!tfr_stb[NFF])&&(tfr_stb[(NFF-1)]);

	// Create an acknowledgement for the return trip
	reg	[(NFF-2):0]	tfr_ack;
	initial	{ lcl_ack, tfr_ack } = 0;
	always @(posedge i_src_clk)
		{ lcl_ack, tfr_ack } <= { tfr_ack[(NFF-2):0], (tfr_stb[NFF]) };

`ifdef	FORMAL
	reg	f_past_valid_src, f_past_valid_gbl;
	initial	f_past_valid_gbl = 1'b0;
	always @(posedge i_src_clk)
		f_past_valid_gbl <= 1'b1;

	initial	f_past_valid_src = 1'b0;
	always @(posedge i_src_clk)
		f_past_valid_src <= 1'b1;

	always @(*)
	if (!f_past_valid_gbl)
	begin
		assert(lcl_stb == 0);
		assert(tfr_stb == 0);
		assert(tfr_ack == 0);
		assert(lcl_ack == 0);
		assert(o_stb   == 0);
	end

	always @(*)
	if ((lcl_stb)&&(lcl_ack))
		assert((&tfr_stb[NFF-1:0])&&(&tfr_ack));
	always @(*)
	if (o_stb)
		assert(&tfr_stb);

	always @(*)
	if ((|tfr_stb)&&(!tfr_stb[0]))
		assert(&tfr_ack);

	always @(*)
	if ((|tfr_ack)&&(!lcl_ack))
		assert(&tfr_stb);

	always @($global_clock)
	if ((f_past_valid_gbl)&&((tfr_stb!=0)||(tfr_ack != 0)))
		assume(!$rose(i_stb));
`endif
endmodule
