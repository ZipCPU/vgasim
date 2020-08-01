////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	tmdsdecode.v
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Convert incoming TMDS data into usable pixel and packet data.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2020, Gisselquist Technology, LLC
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
module	tmdsdecode(i_clk, i_word, o_ctl, o_aux, o_pix);
	input	wire		i_clk;
	input	wire	[9:0]	i_word;
	output	wire	[1:0]	o_ctl;
	output	wire	[6:0]	o_aux;
	output	wire	[7:0]	o_pix;

	reg	[7:0]	r_pix;
	wire	[9:0]	first_midp;
	wire	[9:0]	brev_word;
	reg	[6:0]	r_aux;
	reg	[1:0]	r_ctl;
	genvar		k;

	assign	first_midp = {
			((i_word[0]) ? (~i_word[9:2]) : (i_word[9:2])),
			i_word[1:0] };

	always @(posedge i_clk)
	begin
		if (first_midp[1])
		begin
			r_pix[0] <= (first_midp[9]);
			r_pix[1] <= (first_midp[8] ^ first_midp[9]);
			r_pix[2] <= (first_midp[7] ^ first_midp[8]);
			r_pix[3] <= (first_midp[6] ^ first_midp[7]);
			r_pix[4] <= (first_midp[5] ^ first_midp[6]);
			r_pix[5] <= (first_midp[4] ^ first_midp[5]);
			r_pix[6] <= (first_midp[3] ^ first_midp[4]);
			r_pix[7] <= (first_midp[2] ^ first_midp[3]);
		end else begin
			r_pix[0] <=  first_midp[9];
			r_pix[1] <= !(first_midp[8] ^ first_midp[9]);
			r_pix[2] <= !(first_midp[7] ^ first_midp[8]);
			r_pix[3] <= !(first_midp[6] ^ first_midp[7]);
			r_pix[4] <= !(first_midp[5] ^ first_midp[6]);
			r_pix[5] <= !(first_midp[4] ^ first_midp[5]);
			r_pix[6] <= !(first_midp[3] ^ first_midp[4]);
			r_pix[7] <= !(first_midp[2] ^ first_midp[3]);
		end
	end

	generate for(k=0; k<10; k=k+1)
		assign brev_word[k] = i_word[9-k];
	endgenerate

	always @(posedge i_clk)
	begin
		r_aux <= 6'h0;
		r_ctl <= 2'b00;
		//
		case(brev_word)
		// 2-bit control period coding
		10'h354: begin r_aux <= 7'h10; r_ctl <= 2'h0; end
		10'h0ab: begin r_aux <= 7'h11; r_ctl <= 2'h1; end
		10'h154: begin r_aux <= 7'h12; r_ctl <= 2'h2; end
		10'h2ab: begin r_aux <= 7'h13; r_ctl <= 2'h3; end
		// TERC4 coding
		10'h29c: begin r_aux <= 7'h20; r_ctl <= 2'h0; end
		10'h263: begin r_aux <= 7'h21; r_ctl <= 2'h1; end
		10'h2e4: begin r_aux <= 7'h22; r_ctl <= 2'h2; end
		10'h2e2: begin r_aux <= 7'h23; r_ctl <= 2'h3; end
		10'h171: begin r_aux <= 7'h24; r_ctl <= 2'h0; end
		10'h11e: begin r_aux <= 7'h25; r_ctl <= 2'h1; end
		10'h18e: begin r_aux <= 7'h26; r_ctl <= 2'h2; end
		10'h13c: begin r_aux <= 7'h27; r_ctl <= 2'h3; end
		// This next pixel is also a guard pixel
		10'h2cc: begin r_aux <= 7'h68; r_ctl <= 2'h0; end
		//
		10'h139: begin r_aux <= 7'h29; r_ctl <= 2'h1; end
		10'h19c: begin r_aux <= 7'h2a; r_ctl <= 2'h2; end
		10'h2c6: begin r_aux <= 7'h2b; r_ctl <= 2'h3; end
		10'h28e: begin r_aux <= 7'h2c; r_ctl <= 2'h0; end
		10'h271: begin r_aux <= 7'h2d; r_ctl <= 2'h1; end
		10'h163: begin r_aux <= 7'h2e; r_ctl <= 2'h2; end
		10'h2c3: begin r_aux <= 7'h2f; r_ctl <= 2'h3; end
		// Guard band characters
		//10'h2cc:r_aux<= 8'h38; // done above
		10'h133: begin r_aux <= 7'h41; r_ctl <= 2'h0; end
		default: begin end
		endcase
	end

	assign	o_ctl  = r_ctl;
	assign	o_aux  = r_aux;
	assign	o_pix  = r_pix;

	// Make verilator happy
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = first_midp[0];
	// verilator lint_on  UNUSED
endmodule
