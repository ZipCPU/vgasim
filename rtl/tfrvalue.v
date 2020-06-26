////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	tfrvalue.v
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Transfer an incrementing value, such as a FIFO's read or
//		write pointers, from one clock to another--such as from a write
//	clock to a read clock or vice versa.
//
//	We'll use a gray code to do the transfer, ensuring that any mistakes
//	in value transfer end up one above or one below the true value.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2020, Gisselquist Technology, LLC
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
`default_nettype none
//
module	tfrvalue(i_aclk, i_value, i_bclk, o_value);
	parameter	NB = 16;
	input	wire			i_aclk, i_bclk;
	input	wire	[(NB-1):0]	i_value;
	output	wire	[(NB-1):0]	o_value;

	(* ASYNC_REG = "TRUE" *) reg	q_tfr, q_ack;
	reg			r_atfr, r_btfr;
	reg			r_aack, r_back;
	reg	[(NB-1):0]	r_aval;
	(* ASYNC_REG = "TRUE" *) reg [(NB-1):0]	r_value;

	initial	r_atfr = 0;
	initial	r_aval = 0;
	always @(posedge i_aclk)
	if (!r_atfr && !r_aack)
	begin
		r_aval <= i_value;
		if (i_value != r_aval)
			r_atfr <= 1'b1;
	end else if (r_aack)
		r_atfr <= 1'b0;


	initial	{ r_btfr, q_tfr } = 0;
	always @(posedge i_bclk)
		{ r_btfr, q_tfr } <= { q_tfr, r_atfr };

	initial	r_value = 0;
	initial	r_back = 0;
	always @(posedge i_bclk)
	if ((r_btfr)&&(!r_back))
	begin
		r_value <= r_aval;
		r_back <= 1'b1;
	end else if (!r_btfr)
		r_back <= 1'b0;

	initial	{ r_aack, q_ack } = 0;
	always @(posedge i_aclk)
		{ r_aack, q_ack } <= { q_ack, r_back };

	assign	o_value = r_value;

`ifdef	FORMAL
	(* gclk *)	reg		gbl_clk;
	localparam	CKBITS = 4;
	(* anyconst *) reg [CKBITS-1:0]	f_astep, f_bstep;
	reg		[CKBITS-1:0]	f_acount, f_bcount;

	always @(*) assume(f_astep <= { 1'b1, {(CKBITS-1){1'b0}} });
	always @(*) assume(f_bstep <= { 1'b1, {(CKBITS-1){1'b0}} });
	always @(*) assume(f_astep > 0);
	always @(*) assume(f_bstep > 0);

	always @(posedge gbl_clk)
	begin
		f_acount <= f_acount + f_astep;
		f_bcount <= f_bcount + f_bstep;
	end

	always @(*)
	begin
		assume(i_aclk == f_acount[CKBITS-1]);
		assume(i_bclk == f_bcount[CKBITS-1]);
	end

	//
	// Valids
	//
	reg	f_past_valida, f_past_validb, f_past_validg;
	initial { f_past_valida, f_past_validb, f_past_validg } = 0;

	always @(posedge gbl_clk)
		f_past_validg <= 1;
	always @(posedge i_aclk)
		f_past_valida <= 1;
	always @(posedge i_bclk)
		f_past_validb <= 1;

	//
	// Contract
	//
	always @(posedge gbl_clk)
	if (f_past_validg && $changed(r_aval))
	begin
		assert(r_aval == $past(i_value));
		assert($past({ r_btfr, q_tfr }) == 0);
		assert($past({ r_aack, q_ack }) == 0);
	end

	always @(posedge i_bclk)
	if (f_past_validb && $changed(o_value))
	begin
		assert(o_value == r_aval);
		assert($stable(r_aval));
	end

	//
	// Synchronous
	//
	always @(posedge gbl_clk)
	if (f_past_validg && !$rose(i_aclk))
	begin
		assume($stable(i_value));
		assert($stable(r_atfr));
		//
		assert($stable(q_ack));
		assert($stable(r_aack));
	end

	always @(posedge gbl_clk)
	if (f_past_validg && !$rose(i_bclk))
	begin
		assert($stable(o_value));
		assert($stable(r_back));
		//
		assert($stable(q_tfr));
		assert($stable(r_btfr));
	end
	//
	// Induction
	//
	always @(*)
	if (!r_atfr && !r_aack)
		assert({q_tfr, r_btfr, q_ack, r_back} == 0);
	always @(*)
	if (r_atfr && r_aack)
		assert({q_tfr, r_btfr, q_ack, r_back} == 4'hf);

	always @(*)
		assert(({ r_btfr, q_tfr, r_atfr } == 0)
			||({ r_btfr, q_tfr, r_atfr } == 3'b001)
			||({ r_btfr, q_tfr, r_atfr } == 3'b011)
			||({ r_btfr, q_tfr, r_atfr } == 3'b111)
			||({ r_btfr, q_tfr, r_atfr } == 3'b110)
			||({ r_btfr, q_tfr, r_atfr } == 3'b100));
		
	always @(*)
		assert(({ r_aack, q_ack, r_back } == 0)
			||({ r_aack, q_ack, r_back } == 3'b001)
			||({ r_aack, q_ack, r_back } == 3'b011)
			||({ r_aack, q_ack, r_back } == 3'b111)
			||({ r_aack, q_ack, r_back } == 3'b110)
			||({ r_aack, q_ack, r_back } == 3'b100));
		
	always @(*)
	if (r_atfr && ({ r_btfr, q_tfr} != 2'b11))
		assert({ r_aack, q_ack, r_back } == 3'b000);

	always @(*)
	if (r_back && ({ r_aack, q_ack} != 2'b11))
		assert({ r_btfr, q_tfr, r_atfr } == 3'b111);

	//
	// Cover
	//
	reg	[1:0]	f_cvr_changes;

	initial	f_cvr_changes = 0;
	always @(posedge i_bclk)
	if (f_past_validb && $changed(o_value) && !(&f_cvr_changes))
		f_cvr_changes <= f_cvr_changes + 1;

	// Takes about 19 clock steps per transfer, or 10 original clocks
	// per transfer
	always @(*)
		cover((f_cvr_changes > 0) && ({ r_atfr, r_aack } == 0));

	always @(*)
		cover((&f_cvr_changes)&& ({ r_atfr, r_aack } ==0));

	// Subcover

`endif
endmodule
