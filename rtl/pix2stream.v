////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	pix2stream.v
//
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
//
// Copyright (C) 2020, Gisselquist Technology, LLC
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
module	pix2stream #(
		parameter	HMODE_WIDTH    = 12,
		parameter [0:0]	OPT_MSB_FIRST  = 1'b1,
		parameter 	BUS_DATA_WIDTH = 32
	) (
		input	wire	i_clk,
		input	wire	i_reset,
		//
		input	wire				S_AXIS_TVALID,
		output	wire				S_AXIS_TREADY,
		input	wire [24-1:0]			S_AXIS_TDATA,
		input	wire 				S_AXIS_TLAST, // Hsync
		input	wire 				S_AXIS_TUSER, // Vsync
		//
		output	wire				M_AXIS_TVALID,
		input	wire				M_AXIS_TREADY,
		output	wire [BUS_DATA_WIDTH-1:0]	M_AXIS_TDATA,	// Color
		output	wire				M_AXIS_TLAST,	// Hsync
		output	wire				M_AXIS_TUSER,	// Vsync
		//
		input	wire	[1:0]			i_mode
		// , input	wire [HMODE_WIDTH-1:0]	i_pixels_per_line
	);
	
	localparam	[1:0]		MODE_UNUSED	= 2'b00,
					MODE_CLR8	= 2'b01,
					MODE_CLR16	= 2'b10,
					MODE_DIRECT	= 2'b11;
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
	reg				clr8_zfull, clr16_zfull, clr_zfull;
	reg				clr_user,    clr_zuser;
	reg				clr_last,    clr_zlast;
	reg				z_valid, next_zvalid;

	reg	[BUS_DATA_WIDTH-1:0]	mem_data;
	reg				mem_user, mem_last, mem_valid;

	////////////////////////////////////////////////////////////////////////
	//
	// Skid buffer
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	skidbuffer #(
		.OPT_OUTREG(1),
		.DW(24+2)
	) tskd (
		.i_clk(i_clk),
		.i_reset(i_reset),
		.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
			.i_data({ S_AXIS_TDATA, S_AXIS_TUSER, S_AXIS_TLAST }),
		.o_valid(skd_valid), .i_ready(skd_ready),
			.o_data({ skd_data, skd_user, skd_last }));

	always @(*)
		skd_ready = !z_valid || z_step;

	////////////////////////////////////////////////////////////////////////
	//
	// Shift register stage
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (skd_valid && skd_ready)
		clr_last <= skd_user || skd_last;

	always @(posedge i_clk)
	if (skd_valid && skd_ready)
		clr_user <= skd_user;

	initial	clr8_valid = 0;
	always @(posedge i_clk)
	begin
		case({ skd_valid && skd_ready, z_step })
		2'b01: clr8_valid <= clr8_valid - BUS_DATA_WIDTH;
		2'b10: clr8_valid <= clr8_valid + 8;
		2'b11: clr8_valid <= clr8_valid + 8 - BUS_DATA_WIDTH;
		default: begin end
		endcase

		if (clr_last)
			clr8_valid <= (skd_valid && skd_ready) ? 8: 0;

		if (i_reset)
			clr8_valid <= 0;

		clr8_valid[2:0] <= 0;
	end

	always @(posedge i_clk)
	if (skd_valid && skd_ready)
		clr8_word <= { skd_data[23:21], skd_data[15:13], skd_data[7:6],
					clr8_word[BUS_DATA_WIDTH-1:8] };

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


	initial	clr16_valid = 0;
	always @(posedge i_clk)
	begin
		case({ skd_valid && skd_ready, z_step })
		2'b01: clr16_valid <= clr16_valid - BUS_DATA_WIDTH;
		2'b10: clr16_valid <= clr16_valid + 16;
		2'b11: clr16_valid <= clr16_valid + 16 - BUS_DATA_WIDTH;
		default: begin end
		endcase

		if (clr_last)
			clr16_valid <= (skd_valid && skd_ready) ? 16: 0;

		if (i_reset)
			clr16_valid <= 0;

		clr16_valid[3:0] <= 0;
	end

	always @(posedge i_clk)
	if (skd_valid && skd_ready)
		clr16_word <= { skd_data[23:19], skd_data[15:10], skd_data[7:3],
					clr16_word[BUS_DATA_WIDTH-1:16] };

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

	initial	clr_valid = 0;
	always @(posedge i_clk)
	begin
		case({ skd_valid && skd_ready, z_step })
		2'b01: clr_valid <= clr_valid - BUS_DATA_WIDTH;
		2'b10: clr_valid <= clr_valid + 32;
		2'b11: clr_valid <= clr_valid + 32 - BUS_DATA_WIDTH;
		default: begin end
		endcase

		if (clr_last)
			clr_valid <= (skd_valid && skd_ready) ? 32: 0;

		if (i_reset)
			clr_valid <= 0;

		clr_valid[4:0] <= 0;
	end

	generate if (BUS_DATA_WIDTH == 32)
	begin
		always @(posedge i_clk)
		if (skd_valid && skd_ready)
			clr_word <= { 8'h0, skd_data[23:0] };

		always @(posedge i_clk)
		if (z_step)
			clr_zmask <= clr_word;

	end  else begin
		always @(posedge i_clk)
		if (skd_valid && skd_ready)
			clr_word <= { 8'h0, skd_data[23:0],
						clr_word[BUS_DATA_WIDTH-1:32] };

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

	always @(*)
	begin
		next_zvalid = clr_last;
		case(i_mode)
		MODE_UNUSED:	if (clr8_zfull)  next_zvalid = 1;
		MODE_CLR8:	if (clr8_zfull)  next_zvalid = 1;
		MODE_CLR16:	if (clr16_zfull) next_zvalid = 1;
		MODE_DIRECT:	if (clr_zfull)   next_zvalid = 1;
		endcase
	end

	initial	clr_zvalid = 0;
	always @(posedge i_clk)
	begin
		if (z_step)
		begin
			clr_zlast  <= clr_last;
			clr_zuser  <= clr_user;
			z_valid <= next_zvalid;
		end else if (c_step)
			z_valid <= 0;

		if (i_reset)
			z_valid <= 0;
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Selection from among the various color maps
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (c_step)
	case(i_mode)
	MODE_UNUSED:	mem_data <= clr8_zmask;
	MODE_CLR8:	mem_data <= clr8_zmask;
	MODE_CLR16:	mem_data <= clr16_zmask;
	MODE_DIRECT:	mem_data <= clr_zmask;
	endcase

	initial	mem_valid = 0;
	always @(posedge i_clk)
	if (i_reset)
		mem_valid <= 0;
	else if (c_step)
		mem_valid <= z_valid;
	else if (M_AXIS_TREADY)
		mem_valid <= 0;

	always @(posedge i_clk)
	if (c_step)
		mem_last <= clr_zlast;
	else if (M_AXIS_TREADY)
		mem_last <= 0;

	always @(posedge i_clk)
	if (c_step)
		mem_user <= clr_zuser;
	else if (M_AXIS_TREADY)
		mem_user <= 0;

	////////////////////////////////////////////////////////////////////////
	//
	//
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	z_step = (next_zvalid && c_step);
	assign	c_step = (!M_AXIS_TVALID || M_AXIS_TREADY);
	assign	M_AXIS_TVALID = mem_valid;
	assign	M_AXIS_TDATA  = mem_data;
	assign	M_AXIS_TLAST  = mem_last;
	assign	M_AXIS_TUSER  = mem_user;

`ifdef	FORMAL
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;
	// VLAST will never be true unless also HLAST
	always @(*)
	if (S_AXIS_TVALID && S_AXIS_TUSER)
		assume(S_AXIS_TLAST);

	always @(*)
	if (M_AXIS_TVALID && M_AXIS_TUSER)
		assert(M_AXIS_TLAST);

	always @(posedge i_clk)
	if (!i_reset)
		assume($stable(i_mode));

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

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assume(!S_AXIS_TVALID);
		assert(!M_AXIS_TVALID);
	end else if ($past(M_AXIS_TVALID && !M_AXIS_TREADY))
	begin
		assert(M_AXIS_TVALID);
		assert($stable(M_AXIS_TDATA));
		assert($stable(M_AXIS_TLAST));
		assert($stable(M_AXIS_TUSER));
	end
`endif
endmodule
