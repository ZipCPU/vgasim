////////////////////////////////////////////////////////////////////////////////
//
// Filename:	bench/rtl/sintable.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	This is a very simple sinewave table lookup approach
//		approach to generating a sine wave.  It has the lowest latency
//	among all sinewave generation alternatives.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022-2025, Gisselquist Technology, LLC
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
// }}}
`default_nettype	none
//
module	sintable #(
		// {{{
	parameter	PW =17, // Number of bits in the input phase
			OW =13 // Number of output bits
		// }}}
	) (
		// {{{
	input	wire			i_clk, i_reset, i_ce,
	input	wire	[(PW-1):0]	i_phase,
	output	reg	[(OW-1):0]	o_val,
	//
	input	wire			i_aux,
	output	reg			o_aux
		// }}}
	);

	// Declare variables
	// {{{
	reg	[(OW-1):0]		tbl	[0:((1<<PW)-1)];
	// }}}
	initial	$readmemh("sintable.hex", tbl);

	// o_val
	// {{{
	initial	o_val = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_val <= 0;
	else if (i_ce)
		o_val <= tbl[i_phase];
	// }}}

	// o_aux
	// {{{
	initial	o_aux = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_aux <= 0;
	else if (i_ce)
		o_aux <= i_aux;
	// }}}

endmodule
