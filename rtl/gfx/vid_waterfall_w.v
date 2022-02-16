////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	vid_waterfall_w.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Writes a water fall display to video memory over a bus.  Hence,
//		given an input stream and video dimensions, this IP simply
//	writes a (vertically) scrolling raster to memory.  When it gets to the
//	end of memory, it starts writing over from the top again.
//
//	A companion IP, vid_waterfall_r, shall read from this same memory in
//	the proper order to view the waterfall.
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
module	vid_waterfall_w #(
		// {{{
		parameter	AW = 28,
		parameter	DW = 32,
		parameter	LGFRAME = 11,
		parameter	LGFIFO  =  9,
		parameter	LGBURST = LGFIFO-1,
		parameter	PW = 8,
		parameter [0:0]	OPT_MSB_FIRST = 1
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		// The incoming data stream
		// {{{
		input	wire		S_AXI_TVALID,
		output	wire		S_AXI_TREADY,
		input	wire [PW-1:0]	S_AXI_TDATA,
		input	wire		S_AXI_TLAST,
		// }}}
		// Video information
		// {{{
		input	wire	[LGFRAME-1:0]	i_height, i_width,
		input	wire	[AW-1:0]	i_baseaddr,

		output	reg	[AW-1:0]	o_first_addr,
		// }}}
		// Outgoing bus master
		// {{{
		output	reg			o_wb_cyc, o_wb_stb,
		output	wire			o_wb_we,
		output	reg	[AW-1:0]	o_wb_addr,
		output	wire	[DW-1:0]	o_wb_data,
		output	wire	[DW/8-1:0]	o_wb_sel,

		input	wire			i_wb_stall,
		input	wire			i_wb_ack,
		input	wire	[DW-1:0]	i_wb_data,
		input	wire			i_wb_err
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	reg	[$clog2(DW)-1:0]	pix_count;
	reg				pix_valid, pix_last;
	wire				pix_ready;
	reg	[DW-1:0]		pix_buffer, pix_data;

	reg			clear_fifo;
	wire	[DW-1:0]	fifo_data;
	wire			fifo_full, fifo_empty;
	wire	[LGFIFO:0]	fifo_fill;

	reg			staging_valid;
	reg	[AW-1:0]	line_addr, last_line;
	reg	[LGFRAME-1:0]	line_num, line_pos, line_step;
	reg			hlast, vlast;
	reg	[DW-1:0]	staging_data;

	wire			new_request;
	reg			last_request, last_ack;
	reg	[LGBURST:0]	wb_outstanding;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step #1 (A): pack pixels together
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	pix_ready = !fifo_full;
	assign	S_AXI_TREADY = 1'b1;

	// pix_count, pix_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		pix_count <= 0;
		pix_valid <= 0;
	end else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		pix_valid <= 0;
		pix_count   <= pix_count + PW;
		if (S_AXI_TLAST || (pix_count + PW >= DW))
		begin
			pix_count   <= 0;
			pix_valid <= 1;
		end
	end else if (pix_ready)
		pix_valid <= 0;
	// }}}

	// pix_buffer, pix_data
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		pix_buffer <= 0;
		pix_data   <= 0;
	end else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		if (OPT_MSB_FIRST)
			pix_buffer <= { pix_buffer[DW-PW-1:0], S_AXI_TDATA };
		else
			pix_buffer <= { S_AXI_TDATA, pix_buffer[DW-1:PW] };

		if (S_AXI_TLAST || (pix_count + PW >= DW))
		begin
			pix_buffer <= 0;
			if (OPT_MSB_FIRST)
				pix_data <= { pix_buffer[DW-PW-1:0],
								S_AXI_TDATA };
			else
				pix_data <= { S_AXI_TDATA,
							pix_buffer[DW-1:PW] };
		end
	end
	// }}}

	// pix_last -- the end of line indicator
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		pix_last <= 0;
	else if (S_AXI_TVALID && S_AXI_TREADY)
		pix_last <= S_AXI_TLAST;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step #2: Write pixel data to a FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// clear_fifo
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		clear_fifo <= 0;
	else if ((o_wb_cyc && i_wb_err)
			|| (pix_valid && !clear_fifo &&fifo_full))
		clear_fifo <= 1;
	else if (pix_valid && fifo_empty && pix_last)
		clear_fifo <= 0;
	// }}}

	sfifo #(
		.BW(DW), .LGFLEN(LGFIFO), .OPT_ASYNC_READ(1'b0)
	) pxfifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || clear_fifo),
		.i_wr(pix_valid), .i_data(pix_data), .o_full(fifo_full),
			.o_fill(fifo_fill),
		.i_rd(!staging_valid || (o_wb_stb && !i_wb_stall)),
			.o_data(fifo_data), .o_empty(fifo_empty)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step #3: Register a value before sending it to the bus
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (i_reset)
		staging_valid <= 0;
	else if (clear_fifo)
		staging_valid <= 0;
	else if (!staging_valid || (o_wb_stb && !i_wb_stall))
		staging_valid <= !fifo_empty;

	always @(posedge i_clk)
	if (i_reset)
		staging_data <= 0;
	else if (clear_fifo)
		staging_data <= 0;
	else if (!staging_valid || (o_wb_stb && !i_wb_stall))
		staging_data <= fifo_data;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step #4: Burst pixel data to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	new_request = (!fifo_empty && staging_valid && !clear_fifo)
				&& (!last_request || fifo_fill[LGBURST]);

	// o_wb_cyc, o_wb_stb
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_wb_err || clear_fifo)
	begin
		o_wb_cyc <= 1'b0;
		o_wb_stb <= 1'b0;
	end else if (o_wb_cyc)
	begin
		if (!o_wb_stb && !i_wb_stall)
			o_wb_stb <= new_request;

		if (i_wb_ack && !o_wb_stb && last_ack && !new_request)
			o_wb_cyc <= 1'b0;
	end else if (fifo_fill[LGBURST])
		{ o_wb_cyc, o_wb_stb } <= 2'b11;
	// }}}

	assign	o_wb_data = staging_data;
	assign	o_wb_we   = 1'b1;
	assign	o_wb_sel  = -1;

	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc)
		wb_outstanding <= 0;
	else case({ o_wb_stb && !i_wb_stall, i_wb_ack })
	2'b10: wb_outstanding <= wb_outstanding + 1;
	2'b01: wb_outstanding <= wb_outstanding - 1;
	default: begin end
	endcase

	// last_request
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc)
		last_request <= 0;
	else if (&wb_outstanding[LGBURST-1:1])
		last_request <= 1;
	else if (hlast && !fifo_fill[LGBURST])
		last_request <= 1;
	else
		last_request <= 0;
	// }}}

	// last_ack
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc)
		last_ack <= 0;
	else if (wb_outstanding >= 2)
		last_ack <= 0;
	else if (o_wb_stb && i_wb_stall)
		last_ack <= 0;
	// }}}

	initial	line_addr = 0;
	initial	line_num  = 0;
	initial	line_pos  = 0;
	initial	o_wb_addr = 0;
	initial	hlast     = 0;
	initial	vlast     = 0;
	initial	o_first_addr = 0;
	always @(posedge i_clk)
	if (i_reset || clear_fifo)
	begin
		// {{{
		line_addr <= i_baseaddr;
		line_num  <= 0;
		line_pos  <= 0;
		o_wb_addr <= i_baseaddr;
		hlast     <= 0;
		vlast     <= 0;
		o_first_addr <= i_baseaddr;
		last_line <= i_baseaddr;
		// }}}
	end else if (o_wb_stb && !i_wb_stall)
	begin
		// {{{
		o_wb_addr <= o_wb_addr + 1;
		line_pos  <= line_pos + 1;

		// Verilator lint_off WIDTH
		line_addr <= last_line + line_step;
		hlast <= (line_pos +2 >= line_step);
		// Verilator lint_on  WIDTH

		if (hlast) // line_pos + 1 >= i_line_step)
		begin
			o_wb_addr <= line_addr;
			line_pos  <= 0;
			line_num  <= line_num + 1;
			// Verilator lint_off WIDTH
			line_addr <= line_addr + line_step;
			// Verilator lint_on  WIDTH
			last_line <= line_addr;
			o_first_addr <= last_line;

			if (i_height == 1)
				vlast <= 1;
			else
				vlast <= line_num == (i_height - 2);

			if (vlast)
			begin
				o_wb_addr <= i_baseaddr;
				line_num  <= 0;
				// Verilator lint_off WIDTH
				line_addr <= i_baseaddr + line_step;
				// Verilator lint_on  WIDTH
			end
		end
		// }}}
	end

	always @(posedge i_clk)
		line_step <= (i_width + (DW/PW)-1) >> $clog2(DW/PW);
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_data };
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

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
		assert(last_ack == (fwb_outstanding + (o_wb_stb ? 1:0)
			== (o_wb_ack ? 1:0));
`endif
// }}}
endmodule
