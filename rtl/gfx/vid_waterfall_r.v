////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	vid_waterfall_r.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	This is the other half of the waterfall logic.  It reads pixel
//		data from the system/memory bus, and uses that to feed an AXI-S
//	video stream.  As with vid_waterfall_w, this is a wishbone
//	implementation.
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
module	vid_waterfall_r #(
		// {{{
		parameter	AW = 28, DW = 32,
				PW = 8,		// Video pixel width
		parameter	LGFRAME = 11,
		parameter	LGFIFO  =  9,
		parameter	LGBURST =  LGFIFO-1,
		parameter [0:0]	OPT_MSB_FIRST = 1'b1,
		parameter [0:0]	OPT_TUSER_IS_SOF = 1'b1,
		parameter [0:0]	OPT_ASYNC_CLOCKS = 1'b1
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_pixclk,
		// Verilator lint_off SYNCASYNCNET
		input	wire		i_reset,
		// Verilator lint_on  SYNCASYNCNET
		// Video information
		// {{{
		input	wire	[LGFRAME-1:0]	i_height, i_width,
		input	wire	[AW-1:0]	i_baseaddr,
						i_first_line,
						i_last_line,
		// }}}
		// Wishbone bus master
		// {{{
		output	reg		o_wb_cyc, o_wb_stb,
		output	wire		o_wb_we,
		output	reg [AW-1:0]	o_wb_addr,
		output	wire [DW-1:0]	o_wb_data,
		output	wire [DW/8-1:0]	o_wb_sel,
		//
		input	wire		i_wb_stall,
		input	wire		i_wb_ack,
		input	wire [DW-1:0]	i_wb_data,
		input	wire		i_wb_err,
		// }}}
		// Outgoing video stream
		// {{{
		output	wire		M_VID_TVALID,
		input	wire		M_VID_TREADY,
		output	wire [PW-1:0]	M_VID_TDATA,
		output	wire		M_VID_TLAST,
		output	wire		M_VID_TUSER
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	reg			last_ack, last_request;
	reg	[LGBURST:0]	wb_outstanding;

	wire				ign_fifo_full, fifo_empty, afifo_empty;
	wire	[LGFIFO:0]		fifo_fill;
	wire	[DW-1:0]		fifo_data, afifo_data;

	wire				afifo_read, fifo_read;
	reg				px_valid;
	reg	[$clog2(DW+1)-1:0]	px_count;
	reg	[DW-1:0]		px_data;
	reg	[LGFRAME-1:0]		m_hpos, m_vpos;
	reg				M_VID_HLAST, M_VID_VLAST;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 1. Issue Wishbone read requests
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	// ... of length 1) a burst, 2) whatever keeps the
	// FIFO from filling, and 3) up until the end of the line

	// o_wb_cyc, o_wb_stb
	// {{{
	always @(posedge i_clk)
	if (i_reset || (o_wb_cyc && i_wb_err))
		{ o_wb_cyc, o_wb_stb } <= 2'b00;
	else if (o_wb_cyc)
	begin
		if (!o_wb_stb || !i_wb_stall)
			o_wb_stb <= !last_request;

		if (i_wb_ack && (!o_wb_stb || !i_wb_stall)
					&& !last_request && last_ack)
			o_wb_cyc <= 1'b0;
	end else if (!fifo_fill[LGBURST])
		{ o_wb_cyc, o_wb_stb } <= 2'b11;
	// }}}

	assign	o_wb_we = 1'b0;
	assign	o_wb_data = 0;
	assign	o_wb_sel  = -1;

	// wb_outstanding
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc || i_wb_err)
		wb_outstanding <= 0;
	else case({ o_wb_stb && !i_wb_stall, i_wb_ack })
	2'b10: wb_outstanding <= wb_outstanding + 1;
	2'b01: wb_outstanding <= wb_outstanding - 1;
	default: begin end
	endcase
	// }}}

	// last_ack
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc || i_wb_err)
		last_ack <= 0;
	else if (wb_outstanding >= 2)
		last_ack <= 0;
	else if (o_wb_stb && i_wb_stall)
		last_ack <= 0;
	else
		last_ack <= (wb_outstanding + (o_wb_stb ? 1:0)
						- (i_wb_ack ? 1:0) <= 1);
	// }}}

	// last_request
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc)
		last_request <= 0;
	else if (wb_outstanding[LGBURST])
		last_request <= 1;
	else if (wb_outstanding + fifo_fill + (o_wb_stb ? 1:0) >= (1<<LGFIFO))
		last_request <= 0;
	else
		last_request <= 1;
	// }}}

	reg			wb_hlast, wb_vlast;
	reg	[LGFRAME-1:0]	wb_hpos, wb_vpos, line_step;
	reg	[AW-1:0]	line_addr;

	always @(posedge i_clk)
		line_step <= (i_width + DW-1) >> $clog2(DW/PW);

	// o_wb_addr
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		wb_hpos <= 0;
		wb_vpos <= 0;
		wb_hlast <= 0;
		wb_vlast <= 0;

		o_wb_addr  <= i_baseaddr;
		// Verilator lint_off WIDTH
		line_addr<= i_baseaddr - line_step;
		// Verilator lint_on  WIDTH
		// }}}
	end else if (o_wb_stb && !i_wb_stall)
	begin
		// {{{
		wb_hpos <= wb_hpos + 1;
		o_wb_addr <= o_wb_addr + 1;
		wb_hlast <= (i_width <= 1) || (wb_hpos + 2 >= i_width);
		if ((line_addr < i_first_line)||(line_addr >= i_last_line))
			line_addr <= i_last_line;

		if (wb_hlast)
		begin
			wb_hpos <= 0;
			wb_vpos <= wb_vpos + 1;

			o_wb_addr <= line_addr;
			// Verilator lint_off WIDTH
			line_addr <= line_addr - line_step;
			// Verilator lint_on  WIDTH
			wb_vlast <= (i_height <= 1) || (wb_vpos + 2>= i_height);
			if (wb_vlast)
			begin
				// Verilator lint_off WIDTH
				line_addr <= i_baseaddr - line_step;
				// Verilator lint_on  WIDTH
				o_wb_addr   <= i_baseaddr;
			end
		end
		// }}}
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 2. Store the pixels into a FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	sfifo #(
		.BW(DW), .LGFLEN(LGFIFO), .OPT_ASYNC_READ(1'b0)
	) pxfifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wr(i_wb_ack), .i_data(i_wb_data), .o_full(ign_fifo_full),
			.o_fill(fifo_fill),
		.i_rd(afifo_read), .o_data(fifo_data), .o_empty(fifo_empty)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 3. Cross clock domains
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire	pix_clk, pix_reset;

	generate if (OPT_ASYNC_CLOCKS)
	begin : GEN_ASYNC_FIFO
		// {{{
		reg		r_pix_reset;
		reg	[2:0]	r_pix_reset_pipe;

		initial	{ r_pix_reset, r_pix_reset_pipe } = -1;
		always @(posedge i_pixclk or posedge i_reset)
		if (i_reset)
			{ r_pix_reset, r_pix_reset_pipe } <= -1;
		else
			{ r_pix_reset, r_pix_reset_pipe } <= { r_pix_reset_pipe, 1'b0 };

		afifo #(
			.WIDTH(DW), .LGFIFO(3)
		) pxfifo (
			// {{{
			.i_wclk(i_clk), .i_wr_reset_n(!i_reset),
			.i_wr(!fifo_read), .i_wr_data(fifo_data),
				.o_wr_full(afifo_full),
			.i_rclk(i_pixclk), .i_rd_reset_n(!pix_reset),
			.i_rd(afifo_read), .o_rd_data(afifo_data),
				.o_rd_empty(afifo_empty)
			// }}}
		);

		wire			afifo_full;

		assign	fifo_read = !fifo_empty && !afifo_full;
		assign	pix_clk   = i_pixclk;
		assign	pix_reset = r_pix_reset;
		// }}}
	end else begin
		// {{{
		assign	pix_clk     = i_clk;
		assign	pix_reset   = i_reset;
		assign	fifo_read   = afifo_read;
		assign	afifo_empty = fifo_empty;
		assign	afifo_data  = fifo_data;
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 3. Unpack the FIFO words into pixels of PW bits each
	// {{{
	// ... and generate an AXI-S video output stream
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	afifo_read = (!M_VID_TVALID || M_VID_TREADY)
			&& ((px_count <= PW) || !px_valid
			|| (M_VID_TVALID && M_VID_TREADY && M_VID_HLAST));

	// px_valid
	// {{{
	initial	px_valid = 0;
	always @(posedge pix_clk)
	if (pix_reset)
		px_valid <= 0;
	else if (!M_VID_TVALID || M_VID_TREADY)
	begin
		if (afifo_read)
			px_valid <= !afifo_empty;
		else
			px_valid <= 1;
	end
	// }}}

	// px_count
	// {{{
	initial	px_count = 0;
	always @(posedge pix_clk)
	if (pix_reset)
		px_count <= DW;
	else if (!M_VID_TVALID || M_VID_TREADY)
	begin
		if (afifo_read)
			px_count <= (afifo_empty) ? 0 : DW;
		else
			px_count <= px_count - PW;
	end
	// }}}

	// px_data
	// {{{
	initial	px_data = 0;
	always @(posedge pix_clk)
	if (pix_reset)
		px_data <= 0;
	else if (!M_VID_TVALID || M_VID_TREADY)
	begin
		if (afifo_read && !afifo_empty)
			px_data <= afifo_data;
		else if (OPT_MSB_FIRST)
			px_data <= { px_data[DW-PW-1:0], {(PW){1'b0}} };
		else
			px_data <= { {(PW){1'b0}}, px_data[DW-1:PW] };
	end
	// }}}

	// M_VID_TVALID, M_VID_TDATA
	// {{{
	assign	M_VID_TVALID = px_valid;

	generate if (OPT_MSB_FIRST)
	begin
		assign M_VID_TDATA = px_data[DW-PW +: PW];
	end else begin
		assign M_VID_TDATA = px_data[0 +: PW];
	end endgenerate
	// }}}

	// m_hpos, m_vpos
	// {{{
	initial	m_hpos = 0;
	initial	m_vpos = 0;
	initial	M_VID_HLAST = 0;
	initial	M_VID_VLAST = 0;
	always @(posedge pix_clk)
	if (pix_reset)
	begin
		m_hpos <= 0;
		m_vpos <= 0;
		M_VID_HLAST <= 0;
		M_VID_VLAST <= 0;
	end else if (M_VID_TVALID && M_VID_TREADY)
	begin
		m_hpos <= m_hpos + 1;
		M_VID_HLAST <= (i_width <= 1) || (m_hpos == i_width-2);
		if (M_VID_HLAST)
		begin
			m_hpos <= 0;
			m_vpos <= m_vpos + 1;
			M_VID_VLAST <= (i_height <= 1) || (m_vpos == i_height-2);
			if (M_VID_VLAST)
				m_vpos <= 0;
		end
	end
	// }}}

	// M_VID_TUSER, M_VID_TLAST
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin
		reg	sof;

		always @(posedge pix_clk)
		if (i_reset)
			sof <= 1;
		else if (M_VID_TVALID && M_VID_TREADY)
		begin
			sof <= M_VID_VLAST && M_VID_HLAST;
		end

		assign	M_VID_TLAST = M_VID_HLAST;
		assign	M_VID_TUSER = sof;
	end else begin
		assign	M_VID_TLAST = M_VID_HLAST && M_VID_VLAST;
		assign	M_VID_TUSER = M_VID_HLAST;
	end endgenerate
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ign_fifo_full };
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
`endif
// }}}
endmodule
