////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	atxfifo.v
//
// Project:	afifo, A formal proof of Cliff Cummings' asynchronous FIFO
//
// Purpose:	This file defines the behaviour of an asynchronous FIFO.
//		It was originally copied from a paper by Clifford E. Cummings
//	of Sunburst Design, Inc.  Since then, many of the variable names have
//	been changed and the logic has been rearranged.  However, the
//	fundamental logic remains the same.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// The Verilog logic for this project comes from the paper by Clifford E.
// Cummings, of Sunburst Design, Inc, titled: "Simulation and Synthesis
// Techniques for Asynchronous FIFO Design".  This paper may be found at
// sunburst-design.com.
//
// Minor edits to that logic have been made by Gisselquist Technology, LLC.
// Gisselquist Technology, LLC, asserts no copywrite or ownership of these
// minor edits.
//
//
//
// The formal properties within this project, contained between the
// `ifdef FORMAL line and its corresponding `endif, are owned by Gisselquist
// Technology, LLC, and Copyrighted as such.  Hence, the following copyright
// statement regarding these properties:
//
// Copyright (C) 2018-2020, Gisselquist Technology, LLC
//
// These properties are free software (firmware): you can redistribute it and/or
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
//
module atxfifo(i_wclk, i_wrst_n, i_wr, i_wdata, o_wfull, o_wfill_level,
		i_rclk, i_rrst_n, i_rd, o_rdata, o_rempty);
	parameter	DSIZE = 2,
			ASIZE = 4;
	localparam	DW = DSIZE,
			AW = ASIZE;
	input	wire			i_wclk, i_wrst_n, i_wr;
	input	wire	[DW-1:0]	i_wdata;
	output	reg			o_wfull;
	output	reg	[AW:0]		o_wfill_level;
	input	wire			i_rclk, i_rrst_n, i_rd;
	output	wire	[DW-1:0]	o_rdata;
	output	reg			o_rempty;

	wire	[AW-1:0]	waddr, raddr;
	wire			wfull_next, rempty_next;
	reg	[AW:0]		wgray, wbin, wq2_rgray, wq1_rgray,
				rgray, rbin, rq2_wgray, rq1_wgray;

`ifndef	F_ABSTRACT
	reg	[DW-1:0]	mem	[0:((1<<AW)-1)];
`endif

	/////////////////////////////////////////////
	//
	//
	// Write logic
	//
	//
	/////////////////////////////////////////////

	//
	// Cross clock domains
	//
	// Cross the read gray pointer into the write clock domain
	initial	{ wq2_rgray,  wq1_rgray } = 0;
	always @(posedge i_wclk or negedge i_wrst_n)
	if (!i_wrst_n)
		{ wq2_rgray, wq1_rgray } <= 0;
	else
		{ wq2_rgray, wq1_rgray } <= { wq1_rgray, rgray };



	wire	[AW:0]		wgraynext, wbinnext;

	// Calculate the next write address, and the next graycode pointer.
	assign	wbinnext  = wbin + { {(AW){1'b0}}, ((i_wr) && (!o_wfull)) };
	assign	wgraynext = (wbinnext >> 1) ^ wbinnext;

	assign	waddr = wbin[AW-1:0];

	// Register these two values--the address and its gray code
	// representation
	initial	{ wbin, wgray } = 0;
	always @(posedge i_wclk or negedge i_wrst_n)
	if (!i_wrst_n)
		{ wbin, wgray } <= 0;
	else
		{ wbin, wgray } <= { wbinnext, wgraynext };

	assign	wfull_next = (wgraynext == { ~wq2_rgray[AW:AW-1],
				wq2_rgray[AW-2:0] });

	//
	// Calculate whether or not the register will be full on the next
	// clock.
	initial	o_wfull = 0;
	always @(posedge i_wclk or negedge i_wrst_n)
	if (!i_wrst_n)
		o_wfull <= 1'b0;
	else
		o_wfull <= wfull_next;

	//
	// Calculate just how full we are
	//
	// We'll allow this to be a clock or two out of date, allowing the
	// feeding circuit to set a threshold to stop with.
	reg	[AW:0]	wq2_rbin;
	integer	g2b;
	always @(*)
	begin
		wq2_rbin[AW] = wq2_rgray[AW];
		for(g2b=AW-1; g2b>=0; g2b=g2b-1)
		begin
			wq2_rbin[g2b] = wq2_rgray[g2b] ^ wq2_rbin[g2b+1];
		end
	end

	initial	o_wfill_level = 0;
	always @(posedge i_wclk or negedge i_wrst_n)
	if (!i_wrst_n)
		o_wfill_level <= 0;
	else
		o_wfill_level <= wbin - wq2_rbin;

`ifndef	ABSTRACT
	//
	// Write to the FIFO on a clock
	always @(posedge i_wclk)
	if ((i_wr)&&(!o_wfull))
		mem[waddr] <= i_wdata;
`endif

	/////////////////////////////////////////////
	//
	//
	// Read logic
	//
	//
	/////////////////////////////////////////////

	//
	// Cross clock domains
	//
	// Cross the write gray pointer into the read clock domain
	initial	{ rq2_wgray,  rq1_wgray } = 0;
	always @(posedge i_rclk or negedge i_rrst_n)
	if (!i_rrst_n)
		{ rq2_wgray, rq1_wgray } <= 0;
	else
		{ rq2_wgray, rq1_wgray } <= { rq1_wgray, wgray };


	wire	[AW:0]		rgraynext, rbinnext;

	// Calculate the next read address,
	assign	rbinnext  = rbin + { {(AW){1'b0}}, ((i_rd)&&(!o_rempty)) };
	// and the next gray code version associated with it
	assign	rgraynext = (rbinnext >> 1) ^ rbinnext;

	// Register these two values, the read address and the gray code version
	// of it, on the next read clock
	//
	initial	{ rbin, rgray } = 0;
	always @(posedge i_rclk or negedge i_rrst_n)
	if (!i_rrst_n)
		{ rbin, rgray } <= 0;
	else
		{ rbin, rgray } <= { rbinnext, rgraynext };

	// Memory read address gray code and pointer calculation
	assign	raddr = rbin[AW-1:0];

	// Determine if we'll be empty on the next clock
	assign	rempty_next = (rgraynext == rq2_wgray);

	initial o_rempty = 1;
	always @(posedge i_rclk or negedge i_rrst_n)
	if (!i_rrst_n)
		o_rempty <= 1'b1;
	else
		o_rempty <= rempty_next;

	//
	// Read from the memory--a clockless read here, clocked by the next
	// read FLOP in the next processing stage (somewhere else)
	//
`ifdef	ABSTRACT
	assign	o_rdata = $anyseq;
	always @($global_clock)
	if ((!o_rempty)&&(!$rose(i_rclk)))
		assume($stable(o_rdata));
`else
	assign	o_rdata = mem[raddr];
`ifdef	FORMAL
	always @($global_clock)
	if ((!o_rempty)&&(!$rose(i_rclk)))
		assert($stable(o_rdata));
`endif
`endif


`ifdef	FORMAL
`ifdef	ATXFIFO
`define	ASSUME	assume
`define	ASSERT	assert
`else
`define	ASSUME	assert
`define	ASSERT	assert
`endif
	//
	// Set up the f_past_valid registers.  We'll need one for each of
	// the three clock domains: write, read, and the global simulation
	// clock.
	//
	reg	f_past_valid_rd, f_past_valid_wr, f_past_valid_gbl;

	initial	f_past_valid_rd  = 0;
	initial	f_past_valid_wr  = 0;
	initial	f_past_valid_gbl = 0;
	always @($global_clock)
		f_past_valid_gbl <= 1'b1;
	always @(posedge i_wclk)
		f_past_valid_wr  <= 1'b1;
	always @(posedge i_rclk)
		f_past_valid_rd  <= 1'b1;

	always @(*)
	if (!f_past_valid_gbl)
		assert((!f_past_valid_wr)&&(!f_past_valid_rd));

`ifdef	ATXFIFO
	////////////////////////////////
	//
	// Setup the two clocks themselves.  We'll assert nothing regarding
	// their relative phases or speeds.
	//
	////////////////////////////////
	//
	localparam	F_CLKBITS=5;
	wire	[F_CLKBITS-1:0]	f_wclk_step, f_rclk_step;
	assign	f_wclk_step = $anyconst;
	assign	f_rclk_step = $anyconst;
	always @(*)
		assume(f_wclk_step != 0);
	always @(*)
		assume(f_rclk_step != 0);

	reg	[F_CLKBITS-1:0]	f_wclk_count, f_rclk_count;

	always @($global_clock)
		f_wclk_count <= f_wclk_count + f_wclk_step;
	always @($global_clock)
		f_rclk_count <= f_rclk_count + f_rclk_step;

	always @(*)
	begin
		assume(i_wclk == f_wclk_count[F_CLKBITS-1]);
		assume(i_rclk == f_rclk_count[F_CLKBITS-1]);
	end

	////////////////////////////////
	//
	// Assumptions regarding the two reset inputs.  We'll insist that
	// the reset inputs follow some external reset logic, and that both
	// may be asynchronously asserted from that external reset wire, and
	// only ever synchronously de-asserted.
	//
	////////////////////////////////
	//
	wire	f_areset_n;
	assign	f_areset_n = $anyseq;

	reg	[1:0]	f_sync_reset_rd, f_sync_reset_wr;

	// Write reset--asynchronously asserted on f_areset_n, synchronously
	// deasserted
	initial	f_sync_reset_wr = 2'b00;
	always @(posedge i_wclk or negedge f_areset_n)
	begin
		if (!f_areset_n)
			f_sync_reset_wr <= 2'b00;
		else
			f_sync_reset_wr <= { f_sync_reset_wr[0], 1'b1 };
	end

	// f_sync_reset_wr can never be in state 2'b10, assert that
	// fact to keep induction working
	always @(*)
		assert(f_sync_reset_wr != 2'b10);

	always @(*)
		assume(i_wrst_n == f_sync_reset_wr[1]);

	// Write reset--asynchronously asserted on f_areset_n, synchronously
	// deasserted
	initial	f_sync_reset_rd = 2'b00;
	always @(posedge i_rclk or negedge f_areset_n)
	begin
		if (!f_areset_n)
			f_sync_reset_rd <= 2'b00;
		else
			f_sync_reset_rd <= { f_sync_reset_rd[0], 1'b1 };
	end
	always @(*)
		assume(i_rrst_n == f_sync_reset_rd[1]);

	// f_sync_reset_rd, like f_sync_reset_wr, can never be in state 2'b10,
	// assert that fact to keep induction working
	always @(*)
		assert(f_sync_reset_rd != 2'b10);
`endif


	////////////////////////////////////////////////////
	//
	// Now let's make some assumptions about how our inputs can only ever
	// change on a clock edge.
	//
	////////////////////////////////////////////////////
	//
	always @($global_clock)
	if (f_past_valid_gbl)
	begin
		if (!$rose(i_wclk))
		begin
			`ASSUME($stable(i_wr));
			`ASSUME($stable(i_wdata));
			`ASSERT($stable(o_wfull)||(!i_wrst_n));
		end

		if ((!$rose(i_rclk))&&($stable(i_rrst_n)))
		begin
			`ASSUME($stable(i_rd));
			`ASSERT((o_rempty)||($stable(o_rdata)));
			`ASSERT((!i_rrst_n)||($stable(o_rempty)));
		end
	end


	////////////////////////////////////////////////////
	//
	// Following any reset, several values must be in a known
	// configuration--including cross clock values.  assert
	// those here to insure a consistent state, to include the
	// states of their cross-clock domain counterparts.
	//
	////////////////////////////////////////////////////
	//
	always @(*)
	if ((!f_past_valid_wr)||(!i_wrst_n))
	begin
		`ASSUME(i_wr == 0);
		//
		`ASSERT(wgray == 0);
		`ASSERT(wbin == 0);
		`ASSERT(wq1_rgray == 0);
		`ASSERT(wq2_rgray == 0);
		`ASSERT(rq1_wgray == 0);
		`ASSERT(rq2_wgray == 0);
		//
		// Given that the reset is pulled all at one time,
		// and given that a read cannot proceed until there's
		// at least one element in the FIFO, then as long as we
		// are in the write reset--all pointers must remain at
		// zero.
		//
		`ASSERT(f_fill == 0);
		`ASSERT(rbin   == 0);
		`ASSERT({ f_w2r_rbin, f_w1r_rbin } == 0);
		`ASSERT({ f_r2w_wbin, f_r2w_wbin } == 0);
	end

	always @(*)
	if ((!f_past_valid_rd)||(!i_rrst_n))
	begin
		`ASSUME(i_rd == 0);
		//
		`ASSERT(rgray == 0);
		`ASSERT(rbin == 0);
		`ASSERT(rq1_wgray == 0);
		`ASSERT(rq2_wgray == 0);
		`ASSERT(wq1_rgray == 0);
		`ASSERT(wq2_rgray == 0);
	end

	////////////////////////////////////////////////////
	//
	// Calculate the fill level of the FIFO.
	//
	////////////////////////////////////////////////////
	//
	//
	// First, let's examine the asynchronous fill.  This is the "true"
	// fill of the FIFO that's never really known in either clock domain,
	// but we can fake it here in our "formal" environment.
	wire	[AW:0]		f_fill;

	assign	f_fill = (wbin - rbin);

	initial	assert(f_fill == 0);
	always @($global_clock)
		`ASSERT(f_fill <= { 1'b1, {(AW){1'b0}} });

	// Any time the FIFO is full, o_wfull should be true.  It may take a
	// clock or two to clear, though, so this is an implication and not
	// an equals.
	always @(*)
	if (f_fill == {1'b1,{(AW){1'b0}}})
		`ASSERT(o_wfull);

	// If the FIFO is about to be full, the logic should be able
	// to detect that condition.
	always @(*)
	if (f_fill == {1'b0,{(AW){1'b1}}})
		`ASSERT((wfull_next)||(!i_wr)||(o_wfull));

	// Any time the FIFO is empty, o_rempty should be true.  It may be
	// asserted true at other times as well (i.e. there's a lag before
	// its cleared), so this is an implication and not an equals.
	always @(*)
	if (f_fill == 0)
		`ASSERT(o_rempty);

	// If the FIFO is about to be empty, the logic should be able
	// to detect that condition as well.
	always @(*)
	if (f_fill == 1)
		`ASSERT((rempty_next)||(!i_rd)||(o_rempty));

	// The "wgray" variable should be a gray-coded copy of the binary
	// address wbin.
	always @(*)
		`ASSERT(wgray == ((wbin>>1)^wbin));
	// Same for rgray, the read gray register
	always @(*)
		`ASSERT(rgray == ((rbin>>1)^rbin));

	// The indication that the FIFO is full is that wgray and rgray are
	// equal--save that the top two bits of wgray need to be flipped for
	// this comparison.  See the paper for the details of this operation,
	// and why flipping these bits is necessary.
	always @(*)
	`ASSERT( (rgray == { ~wgray[AW:AW-1], wgray[AW-2:0] })
		== (f_fill == { 1'b1, {(AW){1'b0}} }) );

	// The gray pointers should only ever equal if the FIFO is empty,
	// hence the fill should be zero
	always @(*)
		`ASSERT((rgray == wgray) == (f_fill == 0));

	////////
	//
	// Now repeat, but this time from the reader or writers perspective
	//
	////////
	reg	[AW:0]	f_w2r_rbin, f_w1r_rbin,
			f_r2w_wbin, f_r1w_wbin;
	wire	[AW:0]	f_w2r_fill, f_r2w_fill;

	// Cross the binary value across clock domains.  Since this is formal,
	// and not real hardware, there's no metastability concerns requiring
	// grayscale.  Hence we can cross the full binary (address count) value
	always @(posedge i_wclk or negedge i_wrst_n)
	if (!i_wrst_n)
		{ f_w2r_rbin, f_w1r_rbin } <= 0;
	else
		{ f_w2r_rbin, f_w1r_rbin } <= { f_w1r_rbin, rbin };

	always @(posedge i_rclk or negedge i_rrst_n)
	if (!i_rrst_n)
		{ f_r2w_wbin, f_r1w_wbin } <= 0;
	else
		{ f_r2w_wbin, f_r1w_wbin } <= { f_r1w_wbin, wbin };

	//
	// Now calculate the fill from the perspective of each of the two
	// clock domains
	assign	f_w2r_fill = wbin - f_w2r_rbin;
	assign	f_r2w_fill = f_r2w_wbin - rbin;

// always @(posedge i_wclk)
// if ((f_past_valid_wr)&&(wbin==5)&&(i_wrst_n))
// assert(o_wfill_level == $past(f_w2r_fill));

	// And assert that the fill is always less than or equal to full.
	// This catches underrun as well as overflow, since underrun will
	// look like the fill suddenly increases
	always @(*)
		`ASSERT(f_w2r_fill <= { 1'b1, {(AW){1'b0}} });
	always @(*)
		`ASSERT(f_r2w_fill <= { 1'b1, {(AW){1'b0}} });

	// From the writers perspective, anytime the gray pointers are
	// equal save for the top bit, the FIFO is full and should be asserted
	// as such.  It is possible for the FIFO to be asserted as full at
	// some other times as well.
	always @(*)
	if (wgray == { ~wq2_rgray[AW:AW-1], wq2_rgray[AW-2:0] })
		`ASSERT(o_wfull);

	// The same basic principle applies to the reader as well.  From the
	// readers perspective, anytime the gray pointers are equal the FIFO
	// is empty, and should be asserted as such.
	always @(*)
	if (rgray == rq2_wgray)
		`ASSERT(o_rempty);

	////////////////////////////////////////////////////
	//
	// One of the keys properties of this algorithm is that
	// no more than one bit of the gray coded values will ever
	// change from one clock and clock domain to the next.
	// Since this is a fundamental property of this algorithm,
	// let's make certain the algorithm is operating as we think
	// it should.
	//
	////////////////////////////////////////////////////
	//
	//
`ifdef	ONEHOT
	always @(*)
		assert((wgray == wgray_next)
			||($onehot(wgray ^ wgray_next)));
	always @(*)
		assert((rq2_wgray == rq1_wgray)
			||($onehot(rq2_wgray ^ rq1_wgray)));
`else
	genvar	k;
	generate for(k=0; k<= AW; k=k+1)
	begin : CHECK_ONEHOT_WGRAY
		always @(*)
			`ASSERT((wgray[k] == wgraynext[k])
				||(wgray ^ wgraynext ^ (1<<k) == 0));
		always @(*)
			`ASSERT((rq2_wgray[k] == rq1_wgray[k])
				||(rq2_wgray ^ rq1_wgray ^ (1<<k) == 0));
	end endgenerate
`endif

`ifdef ONEHOT
	always @(*)
		assert((rgray == rgray_next)
			||($onehot(rgray ^ rgray_next)));
	always @(*)
		assert((wq2_rgray == wq1_rgray)
			||($onehot(wq2_rgray ^ wq1_rgray)));
`else
	genvar	k;
	generate for(k=0; k<= AW; k=k+1)
	begin : CHECK_ONEHOT_RGRAY
		always @(*)
			`ASSERT((rgray[k] == rgraynext[k])
				||(rgray ^ rgraynext ^ (1<<k) == 0));
		always @(*)
			`ASSERT((wq2_rgray[k] == wq1_rgray[k])
				||(wq2_rgray ^ wq1_rgray ^ (1<<k) == 0));
	end endgenerate
`endif

`ifdef	ATXFIFO
	////////////////////////////////////////////////////
	//
	// Some cover statements, to make sure valuable states
	// are even reachable
	//
	////////////////////////////////////////////////////
	//

	// Make sure a reset is possible in either domain
	always @(posedge i_wclk)
		cover(i_wrst_n);

	always @(posedge i_rclk)
		cover(i_rrst_n);

	always @($global_clock)
	if (f_past_valid_gbl)
		cover((o_rempty)&&(!$past(o_rempty)));

	always @(*)
	if (f_past_valid_gbl)
		cover(o_wfull);

	always @(posedge i_wclk)
	if (f_past_valid_wr)
		cover($past(o_wfull)&&($past(i_wr))&&(o_wfull));

	always @(posedge i_wclk)
	if (f_past_valid_wr)
		cover($past(o_wfull)&&(!o_wfull));

	always @(posedge i_wclk)
		cover((o_wfull)&&(i_wr));

	always @(posedge i_wclk)
		cover(i_wr);

	always @(posedge i_rclk)
		cover((o_rempty)&&(i_rd));
`endif

`endif
endmodule
