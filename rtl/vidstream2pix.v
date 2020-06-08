////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	vidstream2pix.v
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
// Copyright (C) 2020, Gisselquist Technology, LLC
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
module	vidstream2pix #(
		parameter	HMODE_WIDTH = 12,
		parameter [0:0]	OPT_MSB_FIRST = 1'b1,
		parameter 	BUS_DATA_WIDTH = 32
	) (
		input	wire	i_clk,
		input	wire	i_reset,
		//
		input	wire				S_AXIS_TVALID,
		output	wire				S_AXIS_TREADY,
		input	wire [BUS_DATA_WIDTH-1:0]	S_AXIS_TDATA,
		input	wire 				S_AXIS_TLAST,
		input	wire 				S_AXIS_TUSER,
		//
		output	wire				M_AXIS_TVALID,
		input	wire				M_AXIS_TREADY,
		output	wire	[23:0]			M_AXIS_TDATA,	// Color
		output	wire				M_AXIS_TLAST,	// Hsync
		output	wire				M_AXIS_TUSER,	// Vsync
		//
		input	wire	[2:0]			i_mode,
		input	wire [HMODE_WIDTH-1:0]		i_pixels_per_line,
		//
		input	wire				i_cmap_rd,
		input	wire	[7:0]			i_cmap_raddr,
		output	reg	[23:0]			o_cmap_rdata,
		input	wire				i_cmap_we,
		input	wire	[7:0]			i_cmap_waddr,
		input	wire	[23:0]			i_cmap_wdata,
		input	wire	[2:0]			i_cmap_wstrb
	);
	
	localparam	[2:0]		MODE_BW		= 3'b000,
					MODE_GRAY2	= 3'b001,
					MODE_GRAY4	= 3'b010,
					MODE_CMAP4	= 3'b011,
					MODE_CMAP8	= 3'b100,
					MODE_CLR8	= 3'b101,
					MODE_CLR16	= 3'b110,
					MODE_DIRECT	= 3'b111;
	// Steps:
	//	t_	incoming data
	//	s_	Shift register
	//	c_	Colors
	//	m_	Outgoing data
	localparam	BASE_1 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH- 1) : 0;
	localparam	BASE_2 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH- 2) : 0;
	localparam	BASE_4 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH- 4) : 0;
	localparam	BASE_8 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH- 8) : 0;
	localparam	BASE16 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH-16) : 0;
	localparam	BASE32 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH-32) : 0;

	reg	[23:0]	cmap	[0:255];
	wire				skd_valid, skd_last, skd_user;
	wire	[BUS_DATA_WIDTH-1:0]	skd_data;

	reg				s_valid, skd_ready, s_user, s_last,
					s_last_in_word, s_last_word_in_packet;
	reg [$clog2(BUS_DATA_WIDTH)-1:0] scount;
	reg	[BUS_DATA_WIDTH-1:0]	sreg;
	wire				s_step;

	reg		c_last, c_valid, c_user;
	reg	[23:0]	bw_pix, gray_2, gray_4, cmap_4, cmap_8, clr_8, clr_16,
			direct_clr;
	wire		c_step;

	reg	[23:0]			pix_data;
	reg	[HMODE_WIDTH-1:0]	pix_count;
	reg				pix_user, pix_last, pix_valid;


	integer		k;


	////////////////////////////////////////////////////////////////////////
	//
	// Colormap memory access
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (i_cmap_rd)
		o_cmap_rdata <= cmap[i_cmap_raddr];

	always @(posedge i_clk)
	if (i_cmap_we && i_cmap_wstrb[0])
		cmap[i_cmap_waddr][ 7: 0] <= i_cmap_wdata[ 7: 0];

	always @(posedge i_clk)
	if (i_cmap_we && i_cmap_wstrb[1])
		cmap[i_cmap_waddr][15: 8] <= i_cmap_wdata[15: 8];

	always @(posedge i_clk)
	if (i_cmap_we && i_cmap_wstrb[2])
		cmap[i_cmap_waddr][23:16] <= i_cmap_wdata[23:16];

	////////////////////////////////////////////////////////////////////////
	//
	// Skid buffer
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	skidbuffer #(
		.OPT_OUTREG(1),
		.DW(BUS_DATA_WIDTH+2)
	) tskd (
		.i_clk(i_clk),
		.i_reset(i_reset),
		.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
			.i_data({ S_AXIS_TDATA, S_AXIS_TUSER, S_AXIS_TLAST }),
		.o_valid(skd_valid), .i_ready(skd_ready),
			.o_data({ skd_data, skd_user, skd_last }));

	always @(*)
		skd_ready = !s_valid || (s_step && s_last_in_word);
	////////////////////////////////////////////////////////////////////////
	//
	// Shift register stage
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	s_valid = 0;
	always @(posedge i_clk)
	begin
		if (skd_ready)
		begin
			if (OPT_MSB_FIRST)
			begin
				for(k=0; k<BUS_DATA_WIDTH/8; k=k+1)
					sreg[(BUS_DATA_WIDTH-(k+1)*8) +: 8]
						<= skd_data[k*8 +: 8];
			end else
				sreg    <= skd_data;
			s_valid <= skd_valid;
			s_user  <= skd_user;
			case(i_mode)
			// Verilator lint_off WIDTH
			MODE_BW:	scount <= BUS_DATA_WIDTH - 1;
			MODE_GRAY2:	scount <= BUS_DATA_WIDTH/2 - 1;
			MODE_GRAY4:	scount <= BUS_DATA_WIDTH/4 - 1;
			MODE_CMAP4:	scount <= BUS_DATA_WIDTH/4 - 1;
			MODE_CMAP8:	scount <= BUS_DATA_WIDTH/8 - 1;
			MODE_CLR8:	scount <= BUS_DATA_WIDTH/8 - 1;
			MODE_CLR16:	scount <= BUS_DATA_WIDTH/16 - 1;
			MODE_DIRECT:	scount <= BUS_DATA_WIDTH/32 - 1;
			// Verilator lint_on  WIDTH
			endcase
			s_last_word_in_packet <= (skd_valid) ? skd_last : 0;
			s_last_in_word <= skd_valid && (i_mode == MODE_DIRECT)
					&& (BUS_DATA_WIDTH == 32);
			s_last <= skd_valid && skd_last&&(i_mode == MODE_DIRECT)
					&& (BUS_DATA_WIDTH == 32);
		end else if (s_valid && s_step)
		begin
			if (OPT_MSB_FIRST)
			case(i_mode)
			MODE_BW:	sreg <= sreg << 1;
			MODE_GRAY2:	sreg <= sreg << 2;
			MODE_GRAY4:	sreg <= sreg << 4;
			MODE_CMAP4:	sreg <= sreg << 4;
			MODE_CMAP8:	sreg <= sreg << 8;
			MODE_CLR8:	sreg <= sreg << 8;
			MODE_CLR16:	sreg <= sreg << 16;
			MODE_DIRECT:	begin end
			endcase else case(i_mode)
			MODE_BW:	sreg <= sreg >> 1;
			MODE_GRAY2:	sreg <= sreg >> 2;
			MODE_GRAY4:	sreg <= sreg >> 4;
			MODE_CMAP4:	sreg <= sreg >> 4;
			MODE_CMAP8:	sreg <= sreg >> 8;
			MODE_CLR8:	sreg <= sreg >> 8;
			MODE_CLR16:	sreg <= sreg >> 16;
			MODE_DIRECT:	begin end
			endcase

			if (scount == 0)
				s_valid <= 0;
			if (scount <= 1)
				s_last_in_word <= 1;
			if (scount <= 1)
				s_last <= s_last_word_in_packet;
			if (scount > 0)
				scount <= scount - 1;
		end

		if (i_reset)
		begin
			s_valid <= 0;
			s_last_in_word <= 1;
			s_last_word_in_packet <= 0;
			s_last  <= 0;
		end
	end


	////////////////////////////////////////////////////////////////////////
	//
	// The color stage selects from among the various color mappings
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	c_last = 1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		c_last  <= 1;
		c_valid <= 0;
		c_user  <= 0;
	end else if (s_step)
	begin
		c_last  <= s_last;
		c_valid <= s_valid;
		c_user  <= s_user;
	end

	always @(posedge i_clk)
	if (s_step)
		bw_pix <= sreg[BASE_1] ? 24'hFFFFFF : 24'h000000;

	always @(posedge i_clk)
	if (s_step)
	case(sreg[BASE_2 +: 2])
	2'b00: gray_2 <= 24'h000000;
	2'b01: gray_2 <= 24'h555555;
	2'b10: gray_2 <= 24'haaaaaa;
	2'b11: gray_2 <= 24'hFFFFFF;
	endcase

	always @(posedge i_clk)
	if (s_step)
		gray_4 <= {(6){sreg[BASE_4 +: 4]}};

	always @(posedge i_clk)
	if (s_step)
		cmap_4 <= cmap[{ 4'h0, sreg[BASE_4 +: 4] }];

	always @(posedge i_clk)
	if (s_step)
		cmap_8 <= cmap[sreg[BASE_8 +: 8]];

	always @(posedge i_clk)
	if (s_step)
	begin	// RRR.GGG.BB, 3R, 3G, 2B
		clr_8[23:16] <= {{(2){ sreg[BASE_8+5 +:3]}},sreg[BASE_8+6 +:2]};
		clr_8[15: 8] <= {{(2){ sreg[BASE_8+2 +:3]}},sreg[BASE_8+3 +:2]};
		clr_8[ 7: 0] <= {(4){sreg[BASE_8    +: 2]} };
	end

	always @(posedge i_clk)
	if (s_step)
	begin	// RRRRR.GGGGGG.BBBBB, 5R, 6G, 5B
		clr_16[23:16] <= { sreg[BASE16+11 +: 5], sreg[BASE16+13 +: 3] };
		clr_16[15: 8] <= { sreg[BASE16+ 5 +: 6], sreg[BASE16+ 9 +: 2] };
		clr_16[ 7: 0] <= { sreg[BASE16    +: 5], sreg[BASE16+ 2 +: 3] };
	end

	always @(posedge i_clk)
	if (s_step)
		direct_clr <= sreg[BASE32 +: 24];

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
	MODE_BW:	pix_data <= bw_pix;
	MODE_GRAY2:	pix_data <= gray_2;
	MODE_GRAY4:	pix_data <= gray_4;
	MODE_CMAP4:	pix_data <= cmap_4;
	MODE_CMAP8:	pix_data <= cmap_8;
	MODE_CLR8:	pix_data <= clr_8;
	MODE_CLR16:	pix_data <= clr_16;
	MODE_DIRECT:	pix_data <= direct_clr;
	endcase

	always @(posedge i_clk)
	if (i_reset)
		{ pix_valid, pix_user } <= 2'b00;
	else if (!M_AXIS_TVALID || M_AXIS_TREADY)
	begin
		pix_valid <= c_valid;
		pix_user  <= c_user;
	end

	initial	pix_last  = 1;
	initial	pix_count = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		pix_last  <= 1;
		pix_count <= 0;
		pix_user  <= 0;
	end else if (!M_AXIS_TVALID || M_AXIS_TREADY)
	begin
		if (M_AXIS_TLAST && !c_last)
		begin
			pix_last  <= 0;
			pix_count <= i_pixels_per_line - 1;
			pix_user  <= c_user;
		end else if (!M_AXIS_TLAST)
		begin
			pix_count <= pix_count - 1;
			pix_last  <= c_last || (pix_count <= 1);
		end
	end

	////////////////////////////////////////////////////////////////////////
	//
	//
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	s_step = !c_valid || c_step;
	assign	c_step = (!M_AXIS_TVALID || M_AXIS_TREADY);
	assign	M_AXIS_TVALID = pix_valid;
	assign	M_AXIS_TDATA  = pix_data;
	assign	M_AXIS_TLAST  = pix_last;
	assign	M_AXIS_TUSER  = pix_user;

endmodule
