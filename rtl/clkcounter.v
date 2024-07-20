////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/clkcounter.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Given a clock, asynchronous to the main or system clock, and
//		given a PPS strobe that is synchronous to the main clock, count
//	the number of clock ticks that take place between system clocks.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2017-2024, Gisselquist Technology, LLC
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
`default_nettype	none
// }}}
module	clkcounter #(
		// {{{
		parameter	LGNAVGS = 4,
				BUSW=32
		// }}}
	) (
		// {{{
		// (i_sys_clk, i_sys_pps, i_tst_clk, o_sys_counts);
		input	wire			i_sys_clk, i_sys_pps, i_tst_clk,
		output	wire	[(BUSW-1):0]	o_sys_counts
		// }}}
	);

	// Local declarations
	// {{{
	reg	[(LGNAVGS-1):0]		avgs;
	(* ASYNC_REG = "TRUE" *) reg	q_v, qq_v;
	reg				tst_posedge;
	reg	[(BUSW-LGNAVGS-1):0]	counter;
	reg	[(BUSW-LGNAVGS-1):0]	r_sys_counts;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Divide the test clock by LGNAVGS
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_tst_clk)
		avgs <= avgs + 1'b1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cross clock domains
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_sys_clk)
		q_v <= avgs[(LGNAVGS-1)];
	always @(posedge i_sys_clk)
		qq_v <= q_v;

	always @(posedge i_sys_clk)
		tst_posedge <= (!qq_v)&&(q_v);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Count clock cycles
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_sys_clk)
	if (i_sys_pps)
		counter <= 0;
	else if (tst_posedge)
		counter <= counter + 1'b1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Report the results
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	always @(posedge i_sys_clk)
	if (i_sys_pps)
		r_sys_counts <= counter;

	assign	o_sys_counts = { r_sys_counts, {(LGNAVGS){1'b0}} };
	// }}}
endmodule
