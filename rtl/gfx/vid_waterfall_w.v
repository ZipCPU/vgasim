////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/gfx/vid_waterfall_w.v
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
// Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
		input	wire	[AW-1:0]	i_lastaddr,
		input	wire			i_en,

		output	reg	[AW-1:0]	o_first_line,
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
	wire				wb_reset;
	assign	wb_reset = i_reset || (o_wb_cyc && i_wb_err);

	reg	[$clog2(DW)-1:0]	pix_count;
	reg				pix_valid, pix_last;
	wire				pix_ready;
	reg	[DW-1:0]		pix_buffer, pix_data;

	reg			clear_fifo;
	wire			fifo_rd;
	wire	[DW-1:0]	fifo_data;
	wire			fifo_full, fifo_empty;
	wire	[LGFIFO:0]	fifo_fill;

	reg			staging_valid;
	reg	[AW-1:0]	next_line_addr, this_line;
	reg	[LGFRAME-1:0]	line_pos, line_step;
	reg			hlast, vlast;
	reg	[DW-1:0]	staging_data;

	reg			last_request, last_ack;
	reg	[LGBURST:0]	wb_outstanding;

	reg	[LGFRAME-1:0]	pw_pos;
	reg			pw_last, pw_lastin;

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
	if (i_reset || clear_fifo)
	begin
		pix_count <= 0;
		pix_valid <= 0;
	end else if (S_AXI_TVALID && S_AXI_TREADY && (pix_last || !pw_last))
	begin
		pix_valid <= 0;
		pix_count <= pix_count + PW;
		if ((S_AXI_TLAST || pw_lastin) || (pix_count + PW >= DW))
		begin
			pix_count <= 0;
			pix_valid <= 1;
		end
	end else if (pix_ready)
		pix_valid <= 0;
`ifdef	FORMAL
	always @(*)
	if (!i_reset)
	begin
		assert(pix_count < DW);
		assert((pix_count & ((1<<$clog2(PW))-1)) ==0);
		if (pix_valid)
			assert(pix_count == 0);
	end
`endif
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

	// pw_pos, pw_last, pw_lastin -- trim our input to i_width samples
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_fifo)
	begin
		pw_pos <= 0;
		pw_last <= 0;
		pw_lastin <= 0;
	end else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		pw_lastin <= !S_AXI_TLAST && (pw_pos >= i_width-2);
		if (pix_last || S_AXI_TLAST)
			pw_last <= 0;
		else if (!pw_last)
			pw_last <= pw_lastin;

		if (S_AXI_TLAST)
		begin
			pw_pos <= 0;
		end else if (!pw_last)
			pw_pos <= pw_pos + 1;
	end
`ifdef	FORMAL
	always @(posedge i_clk)
	if (!i_reset)
	begin
		assume($stable(i_width));
		assert(pw_pos <= i_width);
		if (pix_last)
			assert(pw_pos == 0);
		if (pw_last)
			assert(pw_pos == 0 || pw_pos == i_width);
		if (pw_pos == i_width)
		begin
			assert(pw_last);
		end
		assert(pw_lastin == (pw_pos >= i_width-1));
	end
`endif
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
	else if (!i_en || (o_wb_cyc && i_wb_err)
			|| (pix_valid && !clear_fifo && fifo_full))
	begin
		clear_fifo <= 1;
`ifdef	VERILATOR
		if (!clear_fifo)
		$display("WATERFALL-W: Lost sync!");
`endif
	end else if (S_AXI_TVALID && S_AXI_TREADY && S_AXI_TLAST)
	begin
		clear_fifo <= 0;
`ifdef	VERILATOR
		if (clear_fifo) $display("WATERFALL-W: Resync\'d");
`endif
	end
	// }}}

	sfifo #(
		.BW(DW), .LGFLEN(LGFIFO), .OPT_ASYNC_READ(1'b0)
	) pxfifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || clear_fifo),
		.i_wr(pix_valid), .i_data(pix_data), .o_full(fifo_full),
			.o_fill(fifo_fill),
		.i_rd(fifo_rd),
			.o_data(fifo_data), .o_empty(fifo_empty)
		// }}}
	);

	assign	fifo_rd = !staging_valid || (o_wb_stb && !i_wb_stall);
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
	else if (fifo_rd)
		staging_valid <= !fifo_empty;

	always @(posedge i_clk)
	if (i_reset)
		staging_data <= 0;
	else if (clear_fifo)
		staging_data <= 0;
	else if (fifo_rd)
		staging_data <= fifo_data;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step #4: Burst pixel data to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_wb_cyc, o_wb_stb
	// {{{
	initial	{ o_wb_cyc, o_wb_stb } = 2'b00;
	always @(posedge i_clk)
	if (i_reset || i_wb_err || clear_fifo || !i_en)
	begin
		o_wb_cyc <= 1'b0;
		o_wb_stb <= 1'b0;
	end else if (o_wb_cyc)
	begin
		if (o_wb_stb && !i_wb_stall)
			o_wb_stb <= !last_request;

		if (i_wb_ack && last_ack && last_request)
			o_wb_cyc <= 1'b0;
	end else if (fifo_fill[LGBURST])
		{ o_wb_cyc, o_wb_stb } <= 2'b11;
`ifdef	FORMAL
	always @(*)
	if (wb_outstanding == 0 && !o_wb_stb)
		assert(!o_wb_cyc);

	always @(*)
	if (o_wb_stb || fifo_fill > 1)
		assert(staging_valid);
`endif
	// }}}

	assign	o_wb_data = staging_data;
	assign	o_wb_we   = 1'b1;
	assign	o_wb_sel  = -1;

	// wb_outstanding
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc)
		wb_outstanding <= 0;
	else case({ o_wb_stb && !i_wb_stall, i_wb_ack })
	2'b10: wb_outstanding <= wb_outstanding + 1;
	2'b01: wb_outstanding <= wb_outstanding - 1;
	default: begin end
	endcase
	// }}}

	// last_request
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc)
		last_request <= 0;
	else if (&wb_outstanding[LGBURST-1:1])
		last_request <= 1;
	else if (hlast && fifo_fill[LGFIFO:LGBURST] == 0)
		last_request <= 1;
	else if (fifo_fill <= 2)
		last_request <= 1;
	// Once we start a burst, we don't restart it.  We go until done
	// else last_request <= 0;
	// }}}

	// last_ack
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc || !last_request)
		last_ack <= 0;
	else
		last_ack <= (wb_outstanding + (o_wb_stb ? 1:0)
				+ (i_wb_ack ? 0:1) <= 2);
	// }}}

	initial	next_line_addr = 0;
	initial	line_pos  = 0;
	initial	o_wb_addr = 0;
	initial	hlast     = 0;
	initial	vlast     = 0;
	initial	o_first_line = 0;
	always @(posedge i_clk)
	if (i_reset || clear_fifo)
	begin
		// {{{
		line_pos  <= 0;
		o_wb_addr <= i_baseaddr;
		hlast     <= 0;
		vlast     <= 0;
		o_first_line <= i_baseaddr;
		this_line <= i_baseaddr;
		// Verilator lint_off WIDTH
		next_line_addr <= i_baseaddr + line_step;
		// Verilator lint_on  WIDTH
		// }}}
	end else if (o_wb_stb && !i_wb_stall)
	begin
		// {{{
		o_wb_addr <= o_wb_addr + 1;
		line_pos  <= line_pos + 1;

		// Verilator lint_off WIDTH
		hlast <= (line_pos +2 >= line_step);
		// Verilator lint_on  WIDTH

		if (hlast) // line_pos + 1 >= i_line_step)
		begin
			o_wb_addr <= next_line_addr;
			hlast    <= 0;
			line_pos <= 0;
			// Verilator lint_off WIDTH
			if ({ 1'b0, next_line_addr } + (line_step<<1) > { 1'b0, i_lastaddr })
			begin
				next_line_addr <= i_baseaddr;
				vlast <= 1'b1;
			end else begin
				next_line_addr <= next_line_addr + line_step;
				vlast <= 1'b0;
			end

			// Verilator lint_on  WIDTH
			this_line    <= next_line_addr;
			o_first_line <= this_line;
			line_pos  <= 0;

			if (vlast)
			begin
				o_wb_addr <= next_line_addr;
				// Verilator lint_off WIDTH
				next_line_addr <= i_baseaddr + line_step;
				// Verilator lint_on  WIDTH
			end
		end
		// }}}
	end
`ifdef	FORMAL
	always @(*)
	if (o_wb_stb)
		assert(hlast == (line_pos + 1 >= line_step));
`endif

	always @(posedge i_clk)
		line_step <= (i_width*PW + DW-1) >> $clog2(DW);
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_data, wb_reset, i_height };
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
	// {{{
	localparam	F_LGDEPTH = LGBURST+2;
	reg			f_past_valid;
	wire	[F_LGDEPTH-1:0]	fwb_nreqs, fwb_nacks, fwb_outstanding;
	wire			fwb_hlast, fwb_vlast, fwb_sof, fwb_known_height;
	wire	[LGFRAME-1:0]	fwb_xpos, fwb_ypos;
	reg	[LGFRAME-1:0]	f_pktpos;
	wire	[AW:0]	next_line_wide, this_line_wide;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI stream (input) properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *) reg [LGFRAME-1:0]	f_pixwidth;

	always @(*)
	begin
		assume(f_pixwidth >= 4);
		assume(f_pixwidth >= i_width);
	end

	always @(posedge i_clk)
	if (i_reset)
		f_pktpos <= 0;
	else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		if (S_AXI_TLAST)
			f_pktpos <= 0;
		else
			f_pktpos <= f_pktpos + 1;
	end

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!S_AXI_TVALID);
	else if ($past(S_AXI_TVALID && !S_AXI_TREADY))
	begin
		assume(S_AXI_TVALID);
		assume($stable(S_AXI_TDATA));
		assume($stable(S_AXI_TLAST));
	end

	always @(posedge i_clk)
	if (!i_reset && S_AXI_TVALID)
		assume(S_AXI_TLAST == (f_pktpos + 1 == f_pixwidth));

	always @(posedge i_clk)
	if (!i_reset)
		assert(f_pktpos < f_pixwidth);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	fwb_master #(
		// {{{
		.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH),
		.F_OPT_MINCLOCK_DELAY(1'b1)
		// }}}
	) fwb (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(o_wb_cyc), .i_wb_stb(o_wb_stb), .i_wb_we(o_wb_we),
		.i_wb_addr(o_wb_addr), .i_wb_data(o_wb_data),
			.i_wb_sel(o_wb_sel),
		.i_wb_stall(i_wb_stall), .i_wb_ack(i_wb_ack),
			.i_wb_idata(i_wb_data), .i_wb_err(i_wb_err),
		.f_nreqs(fwb_nreqs), .f_nacks(fwb_nacks),
			.f_outstanding(fwb_outstanding)
		// }}}
	);

	always @(posedge i_clk)
	if (!i_reset && o_wb_cyc)
	begin
		if (!last_request || $past(!last_request))
		begin
			assert(!last_ack);
		end else
			assert(last_ack == (fwb_outstanding + (o_wb_stb ? 1:0) <= 1));
	end

	always @(*)
	if (!i_reset && o_wb_cyc && !last_request)
		assert(o_wb_stb);

	always @(*)
	if (!i_reset && wb_outstanding >= (1<<LGBURST))
		assert(!o_wb_stb);

	always @(*)
	if (!i_reset && (&wb_outstanding[LGBURST-1:0]))
		assert(last_request);

	always @(*)
	if (!i_reset && o_wb_cyc)
		assert(wb_outstanding == fwb_outstanding);

	faxivideo #(
		// {{{
		.PW(AW+DW), .LGDIM(LGFRAME), .OPT_TUSER_IS_SOF(1'b0),
		.OPT_SOURCE(1'b0)
		// }}}
	) fvidwb (
		// {{{
		.i_clk(i_clk), .i_reset_n(!wb_reset && !clear_fifo),
		.S_VID_TVALID(o_wb_stb), .S_VID_TREADY(!i_wb_stall),
		.S_VID_TDATA({ o_wb_addr, o_wb_data }),
			.S_VID_TLAST((fwb_ypos+1 == i_height) && hlast),
		.S_VID_TUSER(hlast),
		.i_width(line_step), .i_height(i_height),
		.o_xpos(fwb_xpos), .o_ypos(fwb_ypos),
		.f_known_height(fwb_known_height),
		.o_hlast(fwb_hlast), .o_vlast(fwb_vlast), .o_sof(fwb_sof)
		// }}}
	);

	always @(posedge i_clk)
	if (!i_reset && !clear_fifo)
	begin
		assert(line_pos == fwb_xpos);
		assert(hlast == fwb_hlast);
		assert(vlast == (this_line_wide + line_step > { 1'b0, i_lastaddr }));
		if (vlast)
			assert(next_line_addr == i_baseaddr);
		assert(o_wb_addr == (this_line + line_pos));
		if (!$past(i_reset) && $stable(line_step))
		begin
			if ({ 1'b0, this_line } + (line_step << 1) > { 1'b0, i_lastaddr })
			begin
				assert(next_line_addr == i_baseaddr);
			end else
				assert(next_line_addr == this_line + line_step);
		end

		assert(o_first_line >= i_baseaddr);
		assert(o_first_line <  i_lastaddr);
		assert(o_first_line + line_step <= i_lastaddr);

		assert(this_line >= i_baseaddr);
		assert(this_line <  i_lastaddr);
		assert(this_line + line_step <= i_lastaddr);

	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Video mode assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!i_reset && o_wb_stb)
		assert(staging_valid);

	always @(posedge i_clk)
	if (!i_reset && o_wb_cyc && fifo_fill <= 1)
		assert(last_request);

	assign		next_line_wide = { 1'b0, next_line_addr } + line_step;
	assign		this_line_wide = { 1'b0, this_line } + line_step;

	always @(posedge i_clk)
	if (!i_reset)
	begin
		assume(i_height > 2);
		assume($stable(i_baseaddr));
		assume($stable(i_lastaddr));
		assume($stable(line_step));
		assume(i_baseaddr < i_lastaddr);
		assume(line_step > 2);
		assume({ 4'h0, i_baseaddr } + (line_step << 4) <= { 4'h0, i_lastaddr} );

		assert(this_line_wide <= { 1'b0, i_lastaddr});
		assert(next_line_wide <= { 1'b0, i_lastaddr});

		assert(o_first_line >= i_baseaddr);
		assert(o_first_line <  i_lastaddr);
		assert({ 1'b0, o_first_line } + line_step <=  { 1'b0, i_lastaddr });
		assert(
			// Initial condition
			(o_first_line == this_line
					&& o_first_line == i_baseaddr)
			// Wrap condition, last first_line,
			//	this_line has already wrapped
			|| ({ 1'b0, o_first_line }+ (line_step<<1) > { 1'b0, i_lastaddr }
				&& this_line == i_baseaddr)
			//
			|| { 1'b0, o_first_line } + line_step ==  this_line);
		if (o_first_line == this_line)
			assert(o_first_line == i_baseaddr);
		if (o_first_line != $past(o_first_line))
		begin
			assert((o_first_line == i_baseaddr)
				|| (o_first_line == $past(o_first_line) + line_step));
		end

		if (next_line_addr != i_baseaddr)
			assert(this_line + line_step == next_line_addr);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[1:0]	cvr_frames;
	always @(posedge i_clk)
	if (i_reset)
		cvr_frames <= 0;
	else if (!cvr_frames[1] && o_wb_stb && !i_wb_stall
			&& o_wb_addr == i_lastaddr)
		cvr_frames <= cvr_frames + 1;

	always @(posedge i_clk)
	if (!i_reset)
	begin
		if ($past(!i_reset) && !$past(i_wb_err))
			cover($fell(o_wb_cyc));
		cover(cvr_frames == 1);
		cover(cvr_frames == 2);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	/*
	always @(*)
	begin
		assume(i_baseaddr[7:0] == 0);
		assume(line_step == 11'h100);

		if (!i_reset)
		begin
		assert(o_first_line[7:0] == 0);
		assert(this_line[7:0] == 0);
		assert(next_line_addr[7:0] == 0);
		end
	end
	*/

	// }}}

`endif
// }}}
endmodule
