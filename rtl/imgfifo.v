////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	imgfifo.v
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
// Copyright (C) 2017-2022, Gisselquist Technology, LLC
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
module	imgfifo(i_clk, i_pixclk,
		//
		i_reset, i_newframe, i_baseaddr, i_linewords, i_nlines,
		//
		o_wb_cyc, o_wb_stb, o_wb_addr,
			i_wb_ack, i_wb_err, i_wb_stall, i_wb_data,
		//
		i_rd, o_valid, o_word,
		// 
		o_err);
	parameter	ADDRESS_WIDTH=24, LGFLEN = 11,
			BUSW=32, LW=11;
	localparam	AW=ADDRESS_WIDTH,
			FIFO_ADDRESS_WIDTH=LGFLEN,
			FAW = FIFO_ADDRESS_WIDTH;
	input	wire			i_clk, i_pixclk;
	input	wire			i_reset;
	// verilator lint_off SYNCASYNCNET
	input	wire			i_newframe;
	// verilator lint_on SYNCASYNCNET
	input	wire [(AW-1):0]		i_baseaddr;
	input	wire [LGFLEN:0]		i_linewords;
	input	wire [(LW-1):0]		i_nlines;
	// Wishbone bus commanding
	output	reg			o_wb_cyc, o_wb_stb;
	output	reg [(AW-1):0]		o_wb_addr;
	// Return values on the Wishbone
	input	wire			i_wb_ack;
	input	wire			i_wb_err;
	input	wire			i_wb_stall;
	input	wire	[(BUSW-1):0]	i_wb_data;
	// Now for the interface to the reader on the other end
	input	wire			i_rd;
	output	wire			o_valid;
	output	reg	[(BUSW-1):0]	o_word;
	output	wire			o_err;

	reg	last_ack, last_stb;
	reg	room_for_another_line_in_fifo, end_of_frame;
	reg	[LW-1:0]	vpos;
	wire	[FAW:0]	fifo_availability, fifo_fill;

	reg	[2:0]	wb_reset_pipe;
	wire	wb_reset, pix_reset;

	initial	wb_reset_pipe = -1;
	always @(posedge i_clk or posedge i_reset or posedge i_newframe)
	if (i_reset)
		wb_reset_pipe <= -1;
	else if (i_newframe)
		wb_reset_pipe <= -1;
	else
		wb_reset_pipe <= { wb_reset_pipe[1:0], 1'b0 };
	assign	wb_reset = wb_reset_pipe[2];

	reg	[2:0]	pix_reset_pipe;
	initial	pix_reset_pipe = -1;
	always @(posedge i_pixclk or posedge i_reset)
		if (i_reset)
			pix_reset_pipe <= -1;
		else if (i_newframe)
			pix_reset_pipe <= -1;
		else
			pix_reset_pipe <= { pix_reset_pipe[1:0], 1'b0 };
	assign	pix_reset = (pix_reset_pipe[2]) || (i_newframe);


	initial	o_wb_cyc  = 1'b0;
	initial	o_wb_stb  = 1'b0;
	initial	o_wb_addr = 0;
	always @(posedge  i_clk)
	if ((wb_reset)||(i_wb_err))
	begin
		o_wb_cyc <= 1'b0;
		o_wb_stb <= 1'b0;
		o_wb_addr <= i_baseaddr;
	end else if (o_wb_cyc)
	begin
		if (!i_wb_stall)
			o_wb_stb  <= (o_wb_stb)&&(!last_stb);
		if ((o_wb_stb)&&(!i_wb_stall))
			o_wb_addr <= o_wb_addr + 1'b1;
		if ((i_wb_ack)&&(last_ack))
			o_wb_cyc <= 1'b0;
	end else begin
		if (room_for_another_line_in_fifo)
		begin
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
		end
	end

	reg	[(FAW-1):0]	stb_count;
	initial	stb_count= 0;
	always @(posedge i_clk)
	if ((wb_reset)||(!o_wb_cyc))
		stb_count <= 0;
	else if ((o_wb_stb)&&(!i_wb_stall))
		stb_count <= stb_count + 1'b1;

	initial	last_stb = 1'b0;
	always @(posedge i_clk)
	if ((wb_reset)||(!o_wb_cyc))
		last_stb <= 1'b0;
	else if ((o_wb_stb)&&(!i_wb_stall))
		last_stb <= ({ 2'b0, stb_count } >= { 1'b0, i_linewords}- 2);
	else
		last_stb <= ({ 2'b0, stb_count } >= { 1'b0, i_linewords}- 1'b1);

/*
always @(posedge i_clk)
if (!i_reset)
begin
	assume($stable(i_linewords));
	assume($stable(i_nlines));
end

always @(*)
begin
assert(stb_count <= i_linewords);
if (stb_count == i_linewords)
	assert(!o_wb_stb);
end
*/

	reg	[(FAW-1):0]	ack_count;

	initial	ack_count= 0;
	always @(posedge i_clk)
	if ((wb_reset)||(!o_wb_cyc))
		ack_count <= 0;
	else if (i_wb_ack)
		ack_count <= ack_count + 1'b1;

	initial	last_ack = 1'b0;
	always @(posedge i_clk)
	if ((wb_reset)||(!o_wb_cyc))
		last_ack <= 1'b0;
	else if (i_wb_ack)
		last_ack <= ({2'b00, ack_count} >= {1'b0, i_linewords} - 2);
	else
		last_ack <= ({2'b00, ack_count} >= {1'b0, i_linewords} - 1'b1);

/*
always @(*)
begin
assert(ack_count <= i_linewords);
assert(ack_count <= stb_count);
if (ack_count == i_linewords)
	assert(!o_wb_cyc);
end
*/

	initial	vpos = 0;
	initial	end_of_frame = 0;
	always @(posedge i_clk)
	if ((wb_reset))
	begin
		vpos <= 0;
		end_of_frame <= (i_nlines == 0);
	end else if ((o_wb_cyc)&&(i_wb_ack)&&(last_ack))
	begin
		if (vpos < i_nlines)
			vpos <= vpos + 1'b1;
		end_of_frame <= (i_nlines==0)||(vpos >= i_nlines-1'b1);
	end

/*
always @(*)
begin
	assert(vpos <= i_nlines);
	assert(en_of_frame == (vpos >= i_nlines));
end
*/
	assign	fifo_availability = ({1'b1,{(FAW){1'b0}}} - fifo_fill);

	initial	room_for_another_line_in_fifo = 1'b0;
	always @(posedge i_clk)
	if ((wb_reset))
		room_for_another_line_in_fifo <= 1'b0;
	else if (o_wb_cyc)
		room_for_another_line_in_fifo <= 1'b0;
	else if (!end_of_frame)
		room_for_another_line_in_fifo
			<= (fifo_availability > i_linewords + 1);

	wire	fifo_empty, fifo_full;
	wire	wb_reset_n  = !wb_reset;
	wire	pix_reset_n = !pix_reset;
	atxfifo	#(.DSIZE(BUSW),.ASIZE(FAW))
		fifo(i_clk, wb_reset_n,
			// Incoming (write) data
			(o_wb_cyc)&&(i_wb_ack)&&(!wb_reset), i_wb_data,
			fifo_full, fifo_fill,
			// Outgoing (read) data
			i_pixclk, pix_reset_n, (i_rd)&&(!pix_reset), o_word, fifo_empty);

	assign	o_err = (o_wb_cyc)&&(i_wb_ack)&&(fifo_full);
	assign	o_valid = (!fifo_empty);

`ifdef	FORMAL
`ifdef	IMGFIFO
`define	ASSUME	assume
`define	ASSERT	assert
`else
`define	ASSUME	assert
`define	ASSERT	assume
`endif
	initial	assume(i_reset);

assume property(i_linewords == 1280);
assume property(i_nlines    == 1080);
	//
	// Set up the f_past_valid registers.  We'll need one for each of
	// the three clock domains: write, read, and the global simulation
	// clock.
	//
	reg	f_past_valid_pix, f_past_valid_clk, f_past_valid_gbl;

	initial	f_past_valid_pix  = 0;
	initial	f_past_valid_clk  = 0;
	initial	f_past_valid_gbl = 0;
	always @($global_clock)
		f_past_valid_gbl <= 1'b1;
	always @(posedge i_clk)
		f_past_valid_clk  <= 1'b1;
	always @(posedge i_pixclk)
		f_past_valid_pix  <= 1'b1;

	always @(*)
	if (!f_past_valid_gbl)
		assert((!f_past_valid_clk)&&(!f_past_valid_pix));

	////////////////////////////////
	//
	// Setup the two clocks themselves.  We'll assert nothing regarding
	// their relative phases or speeds.
	//
	////////////////////////////////
	//
	localparam	F_CLKBITS=3;
	wire	[F_CLKBITS-1:0]	f_clk_step, f_pclk_step;
	assign	f_clk_step = $anyconst;
	assign	f_pclk_step = $anyconst;
	always @(*)
		assume(f_clk_step != 0);
	always @(*)
		assume(f_pclk_step != 0);

	reg	[F_CLKBITS-1:0]	f_clk_count, f_pclk_count;

	always @($global_clock)
		f_clk_count <= f_clk_count + f_clk_step;
	always @($global_clock)
		f_pclk_count <= f_pclk_count + f_pclk_step;

	always @(*)
	begin
		assume(i_clk == f_clk_count[F_CLKBITS-1]);
		assume(i_pixclk == f_pclk_count[F_CLKBITS-1]);
	end

	// Insist that items synchronous to the wishbone clock only
	// change on a clock edge
	always @($global_clock)
	if ((f_past_valid_gbl)&&(!$rose(i_clk)))
	begin
		assume($stable(i_reset));
		assume($stable(i_baseaddr));
		assume((i_reset)||($stable(i_linewords)));
		assume((i_reset)||($stable(i_nlines)));
		//
		assume($stable(i_wb_ack));
		assume($stable(i_wb_err));
		assume($stable(i_wb_stall));
		assume($stable(i_wb_data));
	end

	always @(*)
	if (!f_past_valid_clk)
		assume(i_reset);

	always @($global_clock)
	if ((!f_past_valid_gbl)||(!$rose(i_pixclk)))
	begin
		assume($stable(i_rd));
		assume($stable(i_newframe));
	end

	always @(posedge i_clk)
	if ((!f_past_valid_clk)||(!$past(i_reset)))
	begin
		`ASSUME($stable(i_baseaddr));
		`ASSUME($stable(i_linewords));
		`ASSUME($stable(i_nlines));
	end

	always @(posedge i_clk)
	if ((f_past_valid_clk)||(!$past(i_reset)))
	begin
		assume($stable(i_linewords));
		assume($stable(i_nlines));
	end

	//////////////////////////////////////////////
	//////////////////////////////////////////////

	wire	[FAW-1:0]	f_nreqs, f_nacks, f_outstanding;

	fwb_master #(.AW(AW), .DW(BUSW), .F_MAX_STALL(3),
			.F_MAX_ACK_DELAY(5),
			.F_LGDEPTH(FAW),
			.F_OPT_RMW_BUS_OPTION(1'b0),
			.F_OPT_SOURCE(1'b1),
			.F_OPT_DISCONTINUOUS(1'b0),
			.F_OPT_CLK2FFLOGIC(1'b1)
		) f_bus(i_clk, i_reset,
			o_wb_cyc, o_wb_stb, 1'b0, o_wb_addr, 32'h0, 4'h0,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_nreqs, f_nacks, f_outstanding);

	//////////////////////////////////////////////
	//////////////////////////////////////////////

	initial	assume(!i_rd);

	always @(*)
	begin
		assert(stb_count <= i_linewords);
		if (stb_count == i_linewords)
			assert(!o_wb_stb);
		if ((o_wb_cyc)&&(!o_wb_stb))
			assert(stb_count == i_linewords);
	end

	always @(*)
	begin
	assert(ack_count <= i_linewords);
	assert(ack_count <= stb_count);
	if (ack_count == i_linewords)
		assert(!o_wb_cyc);
	end


	always @(*)
	if (o_wb_cyc)
		assert(f_nreqs == stb_count);

	always @(*)
	if (o_wb_cyc)
		assert(f_nacks == ack_count);

	always @(*)
	if ((!end_of_frame)||(o_wb_cyc))
		assume(!i_newframe);

	always @(posedge i_pixclk)
	if (($past(i_newframe))||($past(i_newframe,2)))
		assume(!i_newframe);

	//
	//
	// Let's prove that we'll never overflow our FIFO
	always @(*)
	if ((o_wb_cyc)&&(i_wb_ack))
		assert(!fifo_full);

	// This is going to depend upon some other assertions just to make
	// sure we are always in a state that will never eventually overflow
	reg	[FAW:0]	f_remaining;
	always @(posedge i_clk)
	if (!o_wb_cyc)
		f_remaining <= i_linewords;
	else
		f_remaining <= i_linewords-ack_count;
				/// - (((o_wb_stb)&&(!i_wb_stall))?1:0);
	always @(posedge i_clk)
	if (o_wb_cyc)
		assert({ 1'b0, fifo_availability} > {1'b0,f_remaining});

`endif
endmodule
