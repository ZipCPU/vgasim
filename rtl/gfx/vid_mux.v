////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	vid_mux.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	To select from among many potential video sources, and to do
//		so without ever losing video sync.  Hence, the source selection
//	must take place between frames, and remain AXI stream compliant.
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
module	vid_mux #(
		// {{{
		parameter	NIN = 5,
		parameter	LGDIM = 11,
		parameter	PW = 24,
		parameter [0:0]	OPT_TUSER_IS_SOF = 1
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK, S_AXI_ARESETN,
		//
		input	wire	[NIN-1:0]	S_VID_VALID,
		output	wire	[NIN-1:0]	S_VID_READY,
		input	wire	[NIN*PW-1:0]	S_VID_DATA,
		input	wire	[NIN-1:0]	S_VID_LAST,	// HLAST
		input	wire	[NIN-1:0]	S_VID_USER,	// SOF
		//
		output	reg			M_VID_VALID,
		input	wire			M_VID_READY,
		output	reg	[PW-1:0]	M_VID_DATA,
		output	reg			M_VID_LAST,	// HLAST
		output	reg			M_VID_USER,	// SOF
		//
		input	wire	[$clog2(NIN)-1:0]	i_select
		// }}}
	);

	// local declarations
	// {{{
	reg	[$clog2(NIN)-1:0]	r_framesel;
	reg				adjust_select;
	reg				M_VID_HLAST, M_VID_VLAST;
	wire	[NIN-1:0]		S_VID_HLAST, S_VID_VLAST, S_VID_SOF;
	wire	[NIN-1:0]		new_frame;
	genvar				gk;
	integer				ik;
	// }}}

	// r_framesel
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_framesel <= 0;
	else if (M_VID_VALID && M_VID_HLAST && M_VID_VLAST)
		r_framesel <= i_select;
	// }}}

	// M_VID_VALID
	// {{{
	always @(posedge  S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_VID_VALID <= 0;
	else if (!M_VID_VALID || (M_VID_HLAST && M_VID_VLAST))
		M_VID_VALID <= S_VID_VALID[r_framesel]&& !new_frame[r_framesel];
	// }}}

	// M_VID_DATA
	// {{{
	always @(posedge  S_AXI_ACLK)
	if (!M_VID_VALID || (M_VID_HLAST && M_VID_VLAST))
	begin
		for(ik=0; ik < NIN; ik=ik+1)
		if (r_framesel == ik[$clog2(NIN)-1:0])
			M_VID_DATA <= S_VID_DATA[ik * PW +: PW];
	end
	// }}}

	// M_VID_LAST, M_VID_USER, M_VID_HLAST, M_VID_VLAST
	// {{{
	always @(posedge  S_AXI_ACLK)
	if (!M_VID_VALID || (M_VID_HLAST && M_VID_VLAST))
	begin
		M_VID_LAST <= S_VID_LAST[r_framesel];
		M_VID_USER <= S_VID_USER[r_framesel];
		M_VID_HLAST <= S_VID_HLAST[r_framesel];
		M_VID_VLAST <= S_VID_VLAST[r_framesel];
	end
	// }}}

	// adjust_select
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		adjust_select <= 1;
	else if (M_VID_VALID)
	begin
		adjust_select <= (M_VID_HLAST && M_VID_VLAST)
			&& (i_select != r_framesel)
			&& (i_select < NIN)
			&& (new_frame[i_select]);
	end
	// }}}

	// S_VID_HLAST, S_VID_SOF, S_VID_READY
	// {{{
	generate for(gk=0; gk<NIN; gk=gk+1)
	begin
		if (OPT_TUSER_IS_SOF)
		begin
			// {{{
			reg	[LGDIM-1:0]	height, vpos;
			reg			vlast;

			assign	S_VID_HLAST[gk] = S_VID_LAST[gk];
			assign	S_VID_SOF[gk]   = S_VID_USER[gk];

			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				vpos <= 0;
			else if (S_VID_VALID[gk] && S_VID_READY[gk])
			begin
				if (S_VID_SOF[gk])
				begin
					height <= vpos;
					vpos <= 0;
				end else if (S_VID_HLAST[gk])
					vpos <= vpos + 1;
			end

			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				vlast <= 0;
			else if  (S_VID_VALID[gk] && S_VID_READY[gk])
				vlast <= S_VID_HLAST[gk] && (height == vpos + 1);
			assign	S_VID_VLAST[gk] = vlast;
			// }}}
		end else begin
			// {{{
			reg	sof;

			assign	S_VID_HLAST[gk] = S_VID_USER[gk];
			assign	S_VID_VLAST[gk] = S_VID_LAST[gk];

			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				sof <= 1'b1;
			else if (S_VID_VALID[gk] && S_VID_READY[gk])
				sof <= S_VID_HLAST[gk] && S_VID_VLAST[gk];

			assign	S_VID_SOF = sof;
			// }}}
		end

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			new_frame[gk] <= 1'b1;
		else if (S_VID_VALID[gk] && S_VID_READY[gk])
			new_frame[gk] <= S_VID_HLAST[gk] && S_VID_VLAST[gk];
		else if (S_VID_VALID[gk] && OPT_TUSER_IS_SOF)
			new_frame[gk] <= S_VID_SOF[gk];
		
		always @(*)
		if (adjust_select)
			S_VID_READY[gk] = 1'b0;
		else if (r_framesel == gk)
			S_VID_READY[gk] = !M_VID_VALID || M_VID_READY;
		else
			S_VID_READY[gk] = !new_frame[gk];

	end endgenerate
	// }}}
endmodule
