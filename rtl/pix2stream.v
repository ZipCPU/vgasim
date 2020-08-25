////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	pix2stream.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Converts an AXI-Stream consisting of 24-bit color pixel values
//		into a packed AXI-stream consisting of 32, 64, etc. values
//	suitable for writing to memory.  This includes any color mapping.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020, Gisselquist Technology, LLC
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
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
// }}}
module	pix2stream #(
		// {{{
		parameter	HMODE_WIDTH    = 12,
		parameter 	BUS_DATA_WIDTH = 32
		// }}}
	) (
		// {{{
		input	wire	i_clk,
		input	wire	i_reset,
		// Incoming video data
		// {{{
		input	wire				S_AXIS_TVALID,
		output	wire				S_AXIS_TREADY,
		input	wire [24-1:0]			S_AXIS_TDATA,
		input	wire 				S_AXIS_TLAST, // HLAST
		input	wire 				S_AXIS_TUSER, // VLAST
		// }}}
		// Outgoing video data for the memory bus
		// {{{
		output	wire				M_AXIS_TVALID,
		input	wire				M_AXIS_TREADY,
		output	wire [BUS_DATA_WIDTH-1:0]	M_AXIS_TDATA,	// Color
		output	wire				M_AXIS_TLAST,	// HLAST
		output	wire				M_AXIS_TUSER,	// VLAST
		// }}}
		// Pixel mapping mode control
		// {{{
		input	wire	[1:0]			i_mode
		// , input	wire [HMODE_WIDTH-1:0]	i_pixels_per_line
		// }}}
		// }}}
	);

	localparam	[1:0]		MODE_UNUSED	= 2'b00,
					MODE_CLR8	= 2'b01,
					MODE_CLR16	= 2'b10,
					MODE_DIRECT	= 2'b11;

	// Register/net declarations
	// {{{
	localparam	LGDATA_WIDTH = $clog2(BUS_DATA_WIDTH);
	// Steps:
	//	t_	incoming data
	//	skd_	Shift register inputs
	//	z_	Masked data input (shifted to low order)
	//	c_	Outgoing data

	wire			skd_valid, skd_last, skd_user;
	reg			skd_ready;
	wire	[24-1:0]	skd_data;
	wire			z_step, c_step;

	reg	[BUS_DATA_WIDTH-1:0]	clr8_word, clr8_zmask,
					clr16_word, clr16_zmask,
					clr_word, clr_zmask;

	reg	[$clog2(BUS_DATA_WIDTH):0]	clr8_valid,  clr8_zvalid,
						clr16_valid, clr16_zvalid,
						clr_valid,   clr_zvalid;
	wire				clr8_zfull, clr16_zfull, clr_zfull;
	reg				clr_user,    clr_zuser, clr_full;
	reg				clr_last,    clr_zlast;
	reg				next_zvalid;

	reg	[BUS_DATA_WIDTH-1:0]	mem_data;
	reg				mem_user, mem_last, mem_valid;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Skid buffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
// `ifdef	FORMAL
//	assign	skd_valid = S_AXIS_TVALID;
//	assign	S_AXIS_TREADY = skd_ready;
//	assign	{ skd_data, skd_user, skd_last }
//				= { S_AXIS_TDATA, S_AXIS_TUSER, S_AXIS_TLAST };
// `else
	skidbuffer #(
		.OPT_OUTREG(1),
		.DW(24+2)
`ifdef	FORMAL
		, .OPT_PASSTHROUGH(1)
`endif
	) tskd (
		.i_clk(i_clk),
		.i_reset(i_reset),
		.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
			.i_data({ S_AXIS_TDATA, S_AXIS_TUSER, S_AXIS_TLAST }),
		.o_valid(skd_valid), .i_ready(skd_ready),
			.o_data({ skd_data, skd_user, skd_last }));
// `endif

	always @(*)
		skd_ready = z_step || !clr_full;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Shift register stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// clr_last / HLAST
	// {{{
	initial	clr_last = 0;
	always @(posedge i_clk)
	if (i_reset)
		clr_last <= 0;
	else if (skd_valid && skd_ready)
		clr_last <= (skd_user || skd_last);	// HLAST
	else if (z_step)
		clr_last <= 1'b0;
	// }}}

	// clr_user / VLAST
	// {{{
	initial	clr_user = 0;
	always @(posedge i_clk)
	if (i_reset)
		clr_user <= 0;
	else if (skd_valid && skd_ready)
		clr_user <= skd_user;			// VLAST
	else if (z_step)
		clr_user <= 1'b0;
	// }}}

	//
	// 8b color
	// {{{
	reg	[7:0]	skd_clr8;

	always @(*)
		skd_clr8 = { skd_data[23:21], skd_data[15:13], skd_data[7:6] };

	initial	clr8_valid = 0;
	always @(posedge i_clk)
	begin
		case({ skd_valid && skd_ready, z_step && (clr8_valid >= BUS_DATA_WIDTH) })
		2'b01: clr8_valid <= clr8_valid - BUS_DATA_WIDTH;
		2'b10: clr8_valid <= clr8_valid + 8;
		2'b11: clr8_valid <= clr8_valid + 8 - BUS_DATA_WIDTH;
		default: begin end
		endcase

		if (z_step && clr_last)
			clr8_valid <= (skd_valid && skd_ready) ? 8: 0;

		if (i_reset)
			clr8_valid <= 0;

		clr8_valid[2:0] <= 0;
	end

	always @(posedge i_clk)
	if (skd_valid && skd_ready)
		clr8_word <= { skd_clr8, clr8_word[BUS_DATA_WIDTH-1:8] };

	always @(posedge i_clk)
	if (z_step)
		clr8_zmask <= clr8_word >> (BUS_DATA_WIDTH-clr8_valid);

	initial	clr8_zvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		clr8_zvalid <= 0;
	else if (z_step)
		clr8_zvalid <= clr8_valid;

	assign	clr8_zfull = clr8_zvalid[LGDATA_WIDTH];
	// }}}

	//
	// 16b color
	// {{{
	reg	[15:0]	skd_clr16;

	always @(*)
		skd_clr16 = { skd_data[23:19], skd_data[15:10], skd_data[7:3] };

	initial	clr16_valid = 0;
	always @(posedge i_clk)
	begin
		case({ skd_valid && skd_ready, z_step && (clr16_valid >= BUS_DATA_WIDTH) })
		2'b01: clr16_valid <= clr16_valid - BUS_DATA_WIDTH;
		2'b10: clr16_valid <= clr16_valid + 16;
		2'b11: clr16_valid <= clr16_valid + 16 - BUS_DATA_WIDTH;
		default: begin end
		endcase

		if (z_step && clr_last)	// HLAST, last in group
			clr16_valid <= (skd_valid && skd_ready) ? 16: 0;

		if (i_reset)
			clr16_valid <= 0;

		clr16_valid[3:0] <= 0;
	end

	always @(posedge i_clk)
	if (skd_valid && skd_ready)
		clr16_word <= { skd_clr16, clr16_word[BUS_DATA_WIDTH-1:16] };

	always @(posedge i_clk)
	if (z_step)
		clr16_zmask <= clr16_word >> (BUS_DATA_WIDTH-clr16_valid);

	initial	clr16_zvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		clr16_zvalid <= 0;
	else if (z_step)
		clr16_zvalid <= clr16_valid;

	assign	clr16_zfull = clr16_zvalid[LGDATA_WIDTH];
	// }}}

	//
	// 32b color
	// {{{
	initial	clr_valid = 0;
	always @(posedge i_clk)
	begin
		case({ skd_valid && skd_ready, z_step && (clr_valid >= BUS_DATA_WIDTH) })
		2'b01: clr_valid <= clr_valid - BUS_DATA_WIDTH;
		2'b10: clr_valid <= clr_valid + 32;
		2'b11: clr_valid <= clr_valid + 32 - BUS_DATA_WIDTH;
		default: begin end
		endcase

		if (z_step && clr_last)	// HLAST, last in group
			clr_valid <= (skd_valid && skd_ready) ? 32: 0;

		if (i_reset)
			clr_valid <= 0;

		clr_valid[4:0] <= 0;
	end

	generate if (BUS_DATA_WIDTH == 32)
	begin
		initial	clr_word = 0;
		always @(posedge i_clk)
		if (skd_valid && skd_ready)
			clr_word <= { 8'h0, skd_data[23:0] };

		initial	clr_zmask = 0;
		always @(posedge i_clk)
		if (z_step)
			clr_zmask <= clr_word;

	end  else begin
		initial	clr_word = 0;
		always @(posedge i_clk)
		if (skd_valid && skd_ready)
			clr_word <= { 8'h0, skd_data[23:0],
						clr_word[BUS_DATA_WIDTH-1:32] };

		initial	clr_zmask = 0;
		always @(posedge i_clk)
		if (z_step)
			clr_zmask <= clr_word >> (BUS_DATA_WIDTH-clr_valid);
	end endgenerate

	initial	clr_zvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		clr_zvalid <= 0;
	else if (z_step)
		clr_zvalid <= clr_valid;

	assign	clr_zfull = clr_zvalid[LGDATA_WIDTH];
	// }}}

	//
	// Combined channels
	// {{{
	always @(*)
	begin
		clr_full = clr_last;
		case(i_mode)
		MODE_UNUSED:	if (clr8_valid[LGDATA_WIDTH])  clr_full = 1;
		MODE_CLR8:	if (clr8_valid[LGDATA_WIDTH])  clr_full = 1;
		MODE_CLR16:	if (clr16_valid[LGDATA_WIDTH]) clr_full = 1;
		MODE_DIRECT:	if (clr_valid[LGDATA_WIDTH])   clr_full = 1;
		endcase
	end

	always @(*)
	begin
		next_zvalid = clr_zlast;
		case(i_mode)
		MODE_UNUSED:	if (clr8_zfull)  next_zvalid = 1;
		MODE_CLR8:	if (clr8_zfull)  next_zvalid = 1;
		MODE_CLR16:	if (clr16_zfull) next_zvalid = 1;
		MODE_DIRECT:	if (clr_zfull)   next_zvalid = 1;
		endcase
	end

	initial	clr_zlast  = 0;
	initial	clr_zuser  = 0;
	initial	clr_zvalid = 0;
	always @(posedge i_clk)
	begin
		if (z_step)
		begin
			clr_zlast  <= clr_last;	// HSYNC
			clr_zuser  <= clr_user;	// VSYNC
		end

		if (i_reset)
		begin
			clr_zlast <= 0;
			clr_zuser <= 0;
		end
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Selection from among the various color maps
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (c_step)
	case(i_mode)
	MODE_UNUSED:	mem_data <= clr8_zmask;
	MODE_CLR8:	mem_data <= clr8_zmask;
	MODE_CLR16:	mem_data <= clr16_zmask;
	// MODE_DIRECT:	mem_data <= { clr_zmask[23:0], 8'h00 };
	// MODE_DIRECT:	mem_data <= { clr_zmask[7:0], clr_zmask[15:8], clr_zmask[23:16], 8'h00 };
	MODE_DIRECT:	mem_data <= { 8'h00, clr_zmask[23:0] };
	endcase

	initial	mem_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		mem_valid <= 0;
	else if (c_step)
		mem_valid <= next_zvalid;

	initial	mem_last = 0;
	always @(posedge i_clk)
	if (i_reset)
		mem_last <= 0;
	else if (c_step)
		mem_last <= clr_zlast;

	initial	mem_user = 0;
	always @(posedge i_clk)
	if (i_reset)
		mem_user <= 0;
	else if (c_step)
		mem_user <= clr_zuser;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	z_step = (!next_zvalid || c_step);
	assign	c_step = (!M_AXIS_TVALID || M_AXIS_TREADY);
	assign	M_AXIS_TVALID = mem_valid;
	assign	M_AXIS_TDATA  = mem_data;
	assign	M_AXIS_TLAST  = mem_last;
	assign	M_AXIS_TUSER  = mem_user;
	// }}}
	// Make verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, clr_zmask[31:24] };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;
	integer	ik;
	genvar	gk;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// AXI-Stream Incoming (slave) interface
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assume(!S_AXIS_TVALID);
	end else if ($past(S_AXIS_TVALID && !S_AXIS_TREADY))
	begin
		assume(S_AXIS_TVALID);
		assume($stable(S_AXIS_TDATA));
		assume($stable(S_AXIS_TLAST));
		assume($stable(S_AXIS_TUSER));
	end
	// }}}

	// VLAST will never be true unless also HLAST
	// {{{
	always @(*)
	if (S_AXIS_TVALID && S_AXIS_TUSER)
		assume(S_AXIS_TLAST);
	// }}}

	// AXI-Stream Outgoing (master) interface
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assert(!M_AXIS_TVALID);
	end else if ($past(M_AXIS_TVALID && !M_AXIS_TREADY))
	begin
		assert(M_AXIS_TVALID);
		assert($stable(M_AXIS_TDATA));
		assert($stable(M_AXIS_TLAST));
		assert($stable(M_AXIS_TUSER));
	end
	// }}}

	// VLAST will never be true unless also HLAST
	// {{{
	always @(*)
	if (M_AXIS_TVALID && M_AXIS_TUSER)
		assert(M_AXIS_TLAST);
	// }}}

	always @(posedge i_clk)
	if (!i_reset)
		assume($stable(i_mode));

	always @(*)
	if (!M_AXIS_TVALID)
	begin
		assert(!M_AXIS_TLAST);
		assert(!M_AXIS_TUSER);
	end

	always @(*)
	if (clr_user)
		assert(clr_last);

	always @(*)
	if (clr_zuser)
		assert(clr_zlast);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Never data check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// If S_AXIS_TVALID never goes high, then we should never produce
	// any outputs.  Repeat then with TLAST and TUSER.
	//
	(* anyconst *) reg	no_data, no_last, no_user;

	// assume no inputs, prove no outputs
	// {{{
	always @(*)
	if (no_data)
		assume(!S_AXIS_TVALID || i_reset);

	always @(*)
	if (no_data && !i_reset)
		assert(!M_AXIS_TVALID);
	// }}}

	// assume TLAST is low on the input, prove it's low on the output
	//{{{
	always @(*)
	if (no_last)
		assume(!S_AXIS_TVALID || !S_AXIS_TLAST || i_reset);

	always @(*)
	if (no_last && !i_reset)
		assert(!M_AXIS_TVALID || !M_AXIS_TLAST);

	// Induction
	always @(*)
	if (no_last)
		assert(!clr_last && !clr_zlast);
	// }}}

	// assume TUSER is low on the input, prove it's low on the output
	//{{{
	always @(*)
	if (no_user)
		assume(!S_AXIS_TVALID || !S_AXIS_TUSER || i_reset);

	always @(*)
	if (no_user && !i_reset)
		assert(!M_AXIS_TVALID || !M_AXIS_TUSER);

	// Induction
	always @(*)
	if (no_user)
		assert(!clr_user && !clr_zuser);
	// }}}

	// if clr_valid == 0, then clr_last and clr_user must be zero
	// {{{
	always @(*)
	if (!i_reset) case(i_mode)
	MODE_UNUSED: begin end
	MODE_CLR8:	if (clr8_valid == 0)	assert(!clr_last && !clr_user);
	MODE_CLR16:	if (clr16_valid == 0)	assert(!clr_last && !clr_user);
	MODE_DIRECT:	if (clr_valid == 0)	assert(!clr_last && !clr_user);
	endcase
	// }}}

	// if clr_zvalid == 0, then clr_zlast and clr_zuser must be zero
	// {{{
	always @(*)
	if (!i_reset) case(i_mode)
	MODE_UNUSED: begin end
	MODE_CLR8:	if (clr8_zvalid == 0)	assert(!clr_zlast&& !clr_zuser);
	MODE_CLR16:	if (clr16_zvalid == 0)	assert(!clr_zlast&& !clr_zuser);
	MODE_DIRECT:	if (clr_zvalid == 0)	assert(!clr_zlast&& !clr_zuser);
	endcase
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Negative checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Pick a pixel value--any value.  Prove that if the incoming pixel
	// never matches that pixel value, then the outgoing pixel value
	// won't match either.
	//
	(* anyconst *)	reg		chk_neg_color;
	(* anyconst *)	reg	[31:0]	neg_color;

	// Keep irrelevant neg_color bits at zero
	// {{{
	always @(*)
	case(i_mode)
	MODE_UNUSED: begin end
	MODE_CLR8:	assume(neg_color[31: 8] == 24'h0);
	MODE_CLR16:	assume(neg_color[31:16] == 16'h0);
	MODE_DIRECT:	assume(neg_color[31:26] == 6'h0);
	endcase
	// }}}

	// Assume != neg_color on input
	// {{{
	always @(*)
	if (S_AXIS_TVALID && chk_neg_color) case(i_mode)
	MODE_UNUSED: begin end
	MODE_CLR8:   assume(S_AXIS_TDATA[23:21] != neg_color[7:5]
				|| S_AXIS_TDATA[15:13] != neg_color[4:2]
				|| S_AXIS_TDATA[ 7: 6] != neg_color[1:0]);
	MODE_CLR16:  assume(S_AXIS_TDATA[23:19] != neg_color[15:11]
				|| S_AXIS_TDATA[15:10] != neg_color[10:5]
				|| S_AXIS_TDATA[ 7: 3] != neg_color[ 4:0]);
	MODE_DIRECT: assume({ S_AXIS_TLAST, S_AXIS_TUSER, S_AXIS_TDATA[23:0] }
						!= neg_color[25:0]);
	endcase
	// }}}

	// Contract: assert != neg_color on output
	// {{{
	always @(*)
	if (!i_reset && M_AXIS_TVALID && chk_neg_color) case(i_mode)
	MODE_UNUSED: begin end
	MODE_CLR8:   assert(M_AXIS_TLAST
				||(M_AXIS_TDATA[31:24] != neg_color[7:0]
				&& M_AXIS_TDATA[23:16] != neg_color[7:0]
				&& M_AXIS_TDATA[15:8] != neg_color[7:0]
				&& M_AXIS_TDATA[7:0] != neg_color[7:0]));
	MODE_CLR16:  assert(M_AXIS_TLAST
				||(M_AXIS_TDATA[15:0] != neg_color[15:0]
				&& M_AXIS_TDATA[31:0] != neg_color[15:0]));
	MODE_DIRECT:  if (BUS_DATA_WIDTH == 32)
			assert({ M_AXIS_TLAST, M_AXIS_TUSER,
				M_AXIS_TDATA[23:0] } != neg_color[25:0]);
	endcase
	// }}}

	// Induction, 8b, applied to clr8_word
	// {{{
	always @(*)
	for(ik=0; ik<BUS_DATA_WIDTH; ik=ik+8)
	if (!i_reset && i_mode == 2'b01 && chk_neg_color && (clr8_valid + ik >= BUS_DATA_WIDTH))
		assert(clr8_word[ik +: 8] != neg_color[7:0]);
	// }}}

	// Induction, 16b, applied to clr16_word
	// {{{
	always @(*)
	for(ik=0; ik<BUS_DATA_WIDTH; ik=ik+16)
	if (!i_reset && i_mode == 2'b10 && chk_neg_color && (clr16_valid + ik >= BUS_DATA_WIDTH))
		assert(clr16_word[ik +: 16] != neg_color[15:0]);
	// }}}

	// Induction, 32b, applied to clr32_word
	// {{{
	always @(*)
	if (BUS_DATA_WIDTH == 32)
	for(ik=0; ik<BUS_DATA_WIDTH; ik=ik+32)
	if (!i_reset && i_mode == 2'b11 && chk_neg_color && (clr_valid + ik > 0))
		assert({ clr_last, clr_user, clr_word[ik +: 24] } != neg_color[25:0]);

	always @(*)
	for(ik=0; ik<BUS_DATA_WIDTH; ik=ik+32)
		assert(clr_word[ik + 24 +: 8] == 8'h00);
	// }}}

	// Induction, 8b, applied to clr8_zmask
	// {{{
	always @(*)
	for(ik=0; ik<BUS_DATA_WIDTH; ik=ik+8)
	if (!i_reset && i_mode == 2'b01 && chk_neg_color && ik < clr8_zvalid)
	begin
		if (!clr_zlast)
			assert(clr8_zmask[ik +: 8] != neg_color[7:0]);
	end
	// }}}

	// Induction, 16b, applied to clr16_zmask
	// {{{
	always @(*)
	for(ik=0; ik<BUS_DATA_WIDTH; ik=ik+16)
	if (!i_reset && i_mode == 2'b10 && chk_neg_color && ik < clr16_zvalid)
	begin
		if (!clr_zlast)
			assert(clr16_zmask[ik +: 16] != neg_color[15:0]);
	end
	// }}}

	// Induction, 32b, applied to clr32_zmask
	// {{{
	always @(*)
	if (BUS_DATA_WIDTH == 32)
	for(ik=0; ik<BUS_DATA_WIDTH; ik=ik+32)
	if (!i_reset && i_mode == 2'b11 && chk_neg_color && ik < clr_zvalid)
		assert({ clr_zlast && (ik == 0), clr_zuser && (ik == 0),
				clr_zmask[ik +: 24] } != neg_color[25:0]);

	always @(*)
	for(ik=0; ik<BUS_DATA_WIDTH; ik=ik+32)
		assert(clr_zmask[ik + 24 +: 8] == 8'h00);
	// }}}

	// Induction: Bounds checks on the clr*_?valid signals
	// {{{
	always @(*)
	begin
		assert(clr8_valid[2:0]  == 3'h0);
		assert(clr16_valid[3:0] == 4'h0);
		assert(clr_valid[4:0]   == 5'h0);

		if (!i_reset) case(i_mode)
		MODE_UNUSED:	begin end
		MODE_CLR8:	assert(clr8_valid  <= BUS_DATA_WIDTH);
		MODE_CLR16:	assert(clr16_valid <= BUS_DATA_WIDTH);
		MODE_DIRECT:	assert(clr_valid   <= BUS_DATA_WIDTH);
		endcase
		//
		assert(clr8_zvalid[2:0]  == 3'h0);
		assert(clr16_zvalid[3:0] == 4'h0);
		assert(clr_zvalid[4:0]   == 5'h0);

		if (!i_reset) case(i_mode)
		MODE_UNUSED:	begin end
		MODE_CLR8:	assert(clr8_zvalid  <= BUS_DATA_WIDTH);
		MODE_CLR16:	assert(clr16_zvalid <= BUS_DATA_WIDTH);
		MODE_DIRECT:	assert(clr_zvalid   <= BUS_DATA_WIDTH);
		endcase
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[3:0]	cvr_valid, cvr_lasts, cvr_skid;

	initial	cvr_valid = 0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_valid <= 0;
	else if (M_AXIS_TVALID && M_AXIS_TREADY && !cvr_valid[3])
		cvr_valid <= cvr_valid + 1;

	initial	cvr_lasts = 0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_lasts <= 0;
	else if (M_AXIS_TVALID && M_AXIS_TREADY && M_AXIS_TLAST && !cvr_lasts[3])
		cvr_lasts <= cvr_lasts + 1;

	initial	cvr_skid = 0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_skid <= 0;
	else if (S_AXIS_TVALID && M_AXIS_TREADY && !cvr_skid[3])
		cvr_skid <= cvr_skid + 1;

	generate for(gk=1; gk<4; gk=gk+1)
	begin : CVR_MODE

		(* anyconst *) reg	cvr_chkvalid;
		always @(*)
		if (cvr_chkvalid && S_AXIS_TVALID)
			assume(i_mode == gk[1:0]);

		always @(posedge i_clk)
		if (f_past_valid && !i_reset && i_mode == gk && cvr_chkvalid)
		begin
			cover(cvr_skid[0]);
			cover(cvr_skid[1]);
			cover(cvr_skid[3]);
			//
			cover(cvr_valid[0]);
			cover(cvr_valid[1]);
			cover(cvr_valid[3]);
			cover(cvr_lasts == 1);
			cover(!M_AXIS_TVALID && cvr_valid[3]);
			if (!M_AXIS_TVALID && cvr_valid[3] && $past(M_AXIS_TVALID && M_AXIS_TREADY))
			begin
				cover($past(M_AXIS_TLAST)); // !
				cover($past(M_AXIS_TLAST &&  M_AXIS_TUSER));// !
				cover($past(M_AXIS_TLAST && !M_AXIS_TUSER));// !
			end
		end
	end endgenerate

	always @(*)
	begin
		cover(S_AXIS_TVALID);
		// cover(M_AXIS_TREADY);
		cover(S_AXIS_TVALID && M_AXIS_TREADY);
		cover(cvr_skid[0]);
		cover(cvr_skid[1]);
		cover(cvr_skid[3]);
	end

	always @(posedge i_clk)
	begin
		cover(S_AXIS_TVALID);
		// cover(M_AXIS_TREADY);
		cover(S_AXIS_TVALID && M_AXIS_TREADY);
	end

	always @(posedge i_clk)
	if (f_past_valid)
	begin
		cover(S_AXIS_TVALID);
		// cover(M_AXIS_TREADY);
		cover(S_AXIS_TVALID && M_AXIS_TREADY);

		cover(S_AXIS_TVALID && $past(S_AXIS_TVALID));
		// cover(M_AXIS_TREADY && $past(M_AXIS_TREADY));
		cover(S_AXIS_TVALID && M_AXIS_TREADY
				&& $past(S_AXIS_TVALID && M_AXIS_TREADY));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// always @(*)
		// assume(i_mode != 2'b00);
	// }}}
`endif
// }}}
endmodule
