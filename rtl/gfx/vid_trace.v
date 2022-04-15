////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	vid_trace.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Draw an x-y graph on an outgoing video stream.  The graph will
//		be generated from an incoming AXI Stream, and displayed as a
//	line on the outgoing video stream.
//
//	First version:
//	- Will have no axes, no units, etc.
//	- Will not compress samples.  Samples that do not fit on the screen
//	  will be dropped.
//	- Will plot (up to) the last 2^LGLEN samples.  Samples that arrive
//	  during this time will be buffered for the next plot.  If there aren't
//	  enough for the next plot, then they will be merged with the samples
//	  from the last plot, to create a scrolling effect.
//
//	Possible (eventual) improvements:
//	- Plot a line between the minimum and maximum values received over a
//	  given time.  (min/max compression provided in the stream input, so
//	  S_AXIS_TDATA = { max, min }.)
//	- Control a cursor, to be overlaid on top of the graph
//	- Trigger the collection.  In this case, the design will continuously
//	  draw, until the trigger takes place.  At the trigger, the design
//	  will stop accepting new samples, and instead simply draw the samples
//	  in the buffer until the trigger is (somehow) released.
//	- Interpolation?
//	- Plot multiple traces.  (This can also be done via the overlay.)
//
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
module vid_trace #(
		// {{{
		// LGFRAME: the number of bits required to represent either
		// the width or the height of the video
		parameter	LGFRAME = 11,
		parameter	LGLEN = 10, // Max number of samples per trace
		localparam	LGMEM = LGLEN+1,	// Memory size
		parameter	IW = 12,	// Bits per input sample
		parameter	PW = 2,		// Bits per pixel
		parameter [0:0] OPT_TUSER_IS_SOF = 1'b0,
		// OPT_TRIGGER: True if we want to pause the trace on an
		// external trigger event of some type.
		parameter [0:0] OPT_TRIGGER      = 1'b0,
		// OPT_FRAMED: True if incoming data has a frame to it, so that
		// it must always be displayed in the correct order.  (Think
		// FFT data ...)
		parameter [0:0] OPT_FRAMED       = 1'b0,
		// OPT_UNSIGNED: True if the incoming data is unsigned, and
		// should be plotted bottom to top, with zero at the bottom
		// instead of the middle.
		parameter [0:0] OPT_UNSIGNED     = 1'b0,
		// OPT_LINE: True if you wish to draw lines rather than points
		// to the video
		parameter [0:0] OPT_LINE         = 1'b1,
		parameter [PW-1:0]	BACKGROUND_COLOR = 0,
		parameter [PW-1:0]	AXIS_COLOR =  0,
		parameter [PW-1:0]	LINE_COLOR = -1,
		// HEXTRA is the number of extra (fractional) bits used to
		// divide the width by.  This allows for non-uniform stepping.
		parameter	HEXTRA = 4
		// Optional parameters I may wish to someday incorporate
		// localparam [0:0] OPT_LOWPOWER = 1'b0,
		// localparam [0:0] OPT_SKIDBUFFER = 1'b0,
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK, S_AXI_ARESETN,
		// Control inputs
		input	wire			i_trigger_en,
						i_trigger, i_trigger_reset,
		input	wire	[LGFRAME-1:0]	i_width, i_height,
		// The incoming data stream (AXI-stream format)
		// {{{
		input	wire		S_AXIS_TVALID,
		output	wire		S_AXIS_TREADY,
		input	wire [IW-1:0]	S_AXIS_TDATA,
		input	wire		S_AXIS_TLAST,
		// }}}
		// The outgoing video stream (Video AXI-stream format)
		// {{{
		output	reg		M_VID_VALID,
		input	wire		M_VID_READY,
		output	reg [PW-1:0]	M_VID_DATA,
		output	wire		M_VID_LAST,
		output	wire		M_VID_USER
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	reg	[IW-1:0]	mem	[0:(1<<LGMEM)-1];

	wire			wr_swap_pages;
	reg			wr_mem, wr_page;
	reg	[IW-1:0]	wr_data;
	reg	[LGMEM-1:0]	wr_addr;
	reg	[LGMEM-2:0]	axis_wraddr, axis_rdaddr;
	reg	[LGMEM-1:0]	wr_page_fill;
	wire			frame_syncd;

	reg			rd_vid_flag, rd_valid, rd_eol, rd_vlast, rd_mem,
				mem_eol, mem_vlast;
	reg	[LGFRAME-1:0]	rd_xpos, rd_ypos, mem_xpos, mem_ypos;
	reg	[LGMEM-1:0]	rd_line_addr, rd_rdaddr;
	reg	[LGMEM-2:0]	cp_rdaddr;
	reg	[LGMEM+HEXTRA-1:0]	vid_rdaddr;
	wire	[LGMEM+HEXTRA-1:0]	next_vid_rdaddr;
	// reg	[LGMEM-1:0]	mem_addr;
	reg	[IW-1:0]	mem_value;
	reg	[LGMEM+HEXTRA-1:0]	hdelta;

	reg			rd_src, cp_src, copy_valid;
	wire			copy_ready;
	reg	[LGMEM-2:0]	copy_addr;
	reg	[IW-1:0]	rd_alt, cp_alt;
	wire	[IW-1:0]	rd_value, cp_value;
	wire			rd_ready;


	reg			vs_valid, vs_eol, vs_vlast;
	reg	[LGFRAME-1:0]	vs_xpos, vs_ypos;
	wire			vs_ready;

	wire	[LGFRAME-1:0]	vs_value;
	reg	[LGFRAME-1:0]	vs_scale, vs_min_goal;
	wire	[LGFRAME:0]	vs_posn, vs_abs;


	reg			yp_valid, yp_eol, yp_vlast, yp_sof,
				yp_clipped;
	reg	[LGFRAME-1:0]	yp_xpos, yp_ypos, num_clipped,
				yp_max, yp_value, clip_count;
	wire			yp_ready;

	reg	[LGFRAME-1:0]	m_value;
	reg	M_VID_VLAST, M_VID_HLAST, M_VID_SOF;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Opt.) Trigger handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_TRIGGER)
	begin
		reg	r_triggered, mem_triggered, r_captured;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_triggered <= 1'b0;
		else if (i_trigger_reset || !i_trigger_en)
			r_triggered <= 1'b0;
		else if (i_trigger)
			r_triggered <= 1'b1;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_captured <= 1'b0;
		else if (i_trigger_reset || !i_trigger_en)
			r_captured <= 1'b0;
		else if ((i_trigger || r_triggered) && wr_page_fill[LGMEM-1])
			r_captured <= 1'b1;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			mem_triggered <= 1'b0;
		else if (i_trigger_reset || !i_trigger_en)
			mem_triggered <= 1'b0;
		else if (wr_swap_pages)
			mem_triggered <= r_captured;

		assign	S_AXIS_TREADY = !r_triggered || mem_triggered;

		assign	wr_swap_pages = !mem_triggered
				&& (!rd_valid || rd_ready)
				&& rd_eol && rd_vlast && wr_page_fill[LGMEM-1];

	end else begin

		assign	wr_swap_pages = (!rd_valid || rd_ready)
				&& rd_eol && rd_vlast && wr_page_fill[LGMEM-1];

		assign	S_AXIS_TREADY = 1'b1;

		// Verilator lint_off UNUSED
		wire	unused_trigger;
		assign	unused_trigger = &{ 1'b0, i_trigger_en, i_trigger_reset,
				i_trigger };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	// Store incoming samples into a buffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	//
	//

	// 1. Anytime there's new data, always write to the buffer
	// 2. If there's no new data,
	//       and our page hasn't yet filled,
	//       and we have read a value from the video_page for this purpose,
	//    then write backwards into our buffer an older value.
	// This will help to guarantee that our buffer always has a complete
	// set of data within it.  If it doesn't, we copy from the last buffer
	// one sample at a time until we do have a complete set of data.

	//
	// #M-1.
	//	if (!S_AXI_ARESETN)
	//		clearing_memory <= 1;
	//	else if (r_triggered && i_trigger_reset)
	//		clearing_memory <= 1;
	//	else if (mem_wrflag && &mem_wraddr)
	//		clearing_memory <= 0;
	//
	//	if (!S_AXI_ARESETN)
	//		mem_wrflag <= 0;
	//		mem_wraddr <= 0;
	//		mem_wrdata <= 0;
	//	else if (clearing_memory)
	//		mem_wrflag <= 1'b1;
	//		mem_wraddr <= mem_wraddr + 1;
	//		mem_wrdata <= 0;
	//	else if (S_AXIS_TVALID && S_AXIS_TREADY)
	//		mem_wrflag <= 1'b1;
	//		mem_wraddr <= { wr_page, axis_wraddr };
	//		mem_wrdata <= S_AXIS_TDATA;
	//	else if (copy_valid && copy_addr[LGMEM-1] == wr_page)
	//		mem_wrflag <= 1'b1;
	//		mem_wraddr <= copy_addr;
	//		mem_wrdata <= copy_data;
	//	else
	//		mem_wrflag <= 1'b0;
	//
	//	copy_ready = clearing_memory|| !S_AXIS_TVALID || !S_AXIS_TREADY
	// #M.
	//	if (mem_wrflag)
	//		mem[mem_wraddr] <= mem_wrdata
	//

	// wr_mem: Are we writing to memory on this cycle?
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || wr_swap_pages)
		wr_mem <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY && (!OPT_FRAMED || frame_syncd))
		wr_mem <= 1;
	else if (!OPT_FRAMED && copy_valid && !wr_page_fill[LGMEM-1])
		wr_mem <= 1;
	else
		wr_mem <= 0;
	// }}}

	// wr_data : Data value to write to memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXIS_TVALID && S_AXIS_TREADY && (!OPT_FRAMED || frame_syncd))
		wr_data <= S_AXIS_TDATA;
	else if (!OPT_FRAMED && copy_valid && !wr_page_fill[LGMEM-1])
		wr_data <= cp_value;
	// }}}

	// wr_addr : Where do we write to memory on this sample?
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXIS_TVALID && S_AXIS_TREADY && (!OPT_FRAMED || frame_syncd))
		wr_addr <= { wr_page, axis_wraddr };
	else if (!OPT_FRAMED && copy_valid)
		wr_addr <= { wr_page, copy_addr };
	// }}}

	// wr_page : Which memory page do we write to?
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		wr_page <= 0;
	else if (wr_swap_pages)
		wr_page <= !wr_page;
	// }}}

	always @(posedge S_AXI_ACLK)
	if (wr_mem)
		mem[wr_addr] <= wr_data;

	// axis_wraddr : Where should new data be written to?
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axis_wraddr <= 0;
	else if (wr_swap_pages)
		// Unlike the histogram, we never need to wait for a full
		// page before swapping.
		axis_wraddr <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY && (!OPT_FRAMED || frame_syncd))
		axis_wraddr <= axis_wraddr + 1;
	// }}}

	// axis_rdaddr : Where should reading of this trace begin reading from?
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axis_rdaddr <= 0;
	else if (wr_swap_pages)
		axis_rdaddr <= 0;
	else if (!OPT_FRAMED && !wr_page_fill[LGMEM-1]
				&& copy_valid && copy_ready)
		axis_rdaddr <= axis_rdaddr - 1;
	else if (wr_page_fill[LGMEM-1] && S_AXIS_TVALID && S_AXIS_TREADY
				&& !OPT_FRAMED)
		axis_rdaddr <= axis_rdaddr + 1;
	// }}}

	// wr_page_fill
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || wr_swap_pages)
		wr_page_fill <= 0;
	else if (!wr_page_fill[LGMEM-1])
	begin
		if ((S_AXIS_TVALID && S_AXIS_TREADY
					&& (!OPT_FRAMED || frame_syncd))
				|| (!OPT_FRAMED && copy_valid && copy_ready))
			wr_page_fill <= wr_page_fill + 1;
	end
	// }}}

	assign	copy_ready = (!S_AXIS_TVALID || !S_AXIS_TREADY);

	// frame_syncd
	// {{{
	generate if (OPT_FRAMED)
	begin : GEN_SYNC
		// The goal here is that the first sample of any data frame
		// should be the sample immediately following TLAST.  If we
		// swap at some time other than TLAST, then we need to wait for
		// and skip all samples up to and including the TLAST sample.
		// Once we receive TLAST, we are then synchronized again.
		reg	r_syncd, r_last;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_last <= 1;
		else if (S_AXIS_TVALID && S_AXIS_TREADY)
			r_last <= S_AXIS_TLAST;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_syncd <= 1;
		else if (S_AXIS_TVALID && S_AXIS_TREADY && S_AXIS_TLAST)
			r_syncd <= 1;
		else begin
			// Here's the only time we can lose sync--if we swap
			// pages having not just seen TLAST.  In this case,
			// we'll need to wait for TLAST before we start
			// sampling again.
			if (wr_swap_pages && !r_last)
				r_syncd <= 0;
			//
			// TLAST may show up while the page is filling, that
			// is okay, and won't cause us to lose sync unless
			// we swap pages (above) without being syncd.
			//
			// However, once we fill up, we can't continue to
			// write anymore without losing sync.  That's handled
			// above.
		end

		assign	frame_syncd = r_syncd;
	end else begin : NO_SYNC
		assign	frame_syncd = 1'b1;

		// Verilator lint_off UNUSED
		wire	unused_frame;
		assign	unused_frame = &{ 1'b0, S_AXIS_TLAST, frame_syncd };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	// Generate the outgoing video from the buffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	//
	//

	////////////////////////////////////////////////////////////////////////
	//
	// #1. h_*: Read from memory, calculate read address and purpose
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// next_vid_rdaddr
	// {{{
	assign	next_vid_rdaddr = vid_rdaddr + hdelta;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		vid_rdaddr <= 0;
	else if (wr_swap_pages)
		vid_rdaddr <= { 1'b0, axis_rdaddr, {(HEXTRA){1'b0}} };
	else if (rd_valid && rd_ready)
	begin
		if (rd_eol)
			vid_rdaddr <= { 1'b0, rd_line_addr[LGMEM-2:0],
							{(HEXTRA){1'b0}} };
		else if (!vid_rdaddr[LGMEM+HEXTRA-1])
			vid_rdaddr <= vid_rdaddr + hdelta;
	end
	// }}}

	// rd_eol, rd_xpos, rd_ypos, rd_vlast
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		rd_eol   <= 0;
		rd_xpos  <= 0;
		rd_ypos  <= 0;
		rd_vlast <= 0;
		// }}}
	end else if (rd_valid && rd_ready)
	begin
		// {{{
		rd_eol  <= (rd_xpos >= i_width-2);
		rd_xpos <= rd_xpos + 1;
		if (rd_eol)
		begin
			rd_xpos <= 0;
			rd_eol  <= 0;

			rd_ypos  <= rd_ypos + 1;
			rd_vlast <= (rd_ypos >= i_height-2);

			if (rd_vlast)
			begin
				rd_ypos <= 0;
				rd_vlast <= 0;
			end
		end
		// }}}
	end
	// }}}

	// rd_vid_flag, rd_rdaddr, rd_line_addr, cp_rdaddr
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		rd_vid_flag  <= 1'b1;
		rd_rdaddr    <= 0;
		rd_line_addr <= 0;
		cp_rdaddr    <= 0;
		// }}}
	end else if (wr_swap_pages)
	begin
		// {{{
		rd_mem       <= 1;
		rd_vid_flag  <= 1'b1;
		rd_rdaddr    <= { wr_page, axis_rdaddr };
		rd_line_addr <= { wr_page, axis_rdaddr };
		cp_rdaddr    <= axis_rdaddr -1;
		// }}}
	end else if (!rd_valid || rd_ready)
	begin
		// {{{
		rd_mem <= 1;
		rd_vid_flag <= 1'b1;
		if (!vid_rdaddr[LGMEM+HEXTRA-1])
			rd_rdaddr <= { !wr_page, next_vid_rdaddr[LGMEM+HEXTRA-2:HEXTRA] };

		if (rd_valid && rd_eol)
		begin
			rd_rdaddr <= rd_line_addr;
		end
		// }}}
	end else if (!OPT_FRAMED && (!copy_valid || copy_ready)
						&& !wr_page_fill[LGMEM-1])
	begin // if copy_cycle
		// {{{
		rd_mem <= 1;
		rd_vid_flag <= 1'b0;
		rd_rdaddr <= {  !wr_page, cp_rdaddr };
		cp_rdaddr <= cp_rdaddr - 1;
		// }}}
	end else
		rd_mem <= 0;

	// hdelta tracking loop
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		hdelta <= 1;
	else if (rd_valid && rd_ready && rd_eol)
	begin
		// $display("RDADDR = %5d : %5d, WIDTH = %4d, HDELTA: %2d",
		//	vid_rdaddr[LGMEM+HEXTRA-1:0],
		//	vid_rdaddr[LGMEM+HEXTRA-1:HEXTRA],
		//	i_width, hdelta);

		// Verilator lint_off WIDTH
		if (next_vid_rdaddr[LGMEM+HEXTRA-1])
			hdelta <= hdelta - 1;
		else if ((&hdelta) || (vid_rdaddr[LGMEM + HEXTRA-2:0]
				+ i_width > (1<<(LGMEM+HEXTRA-1))))
		begin
		end else if (vid_rdaddr[LGMEM+HEXTRA-2:HEXTRA] + (i_width<< 2)
					< (1<<(LGMEM-1)))
		begin
			hdelta <= hdelta + (4<<HEXTRA);
		end else
			hdelta <= hdelta + 1;
		// Verilator lint_on  WIDTH
	end
	// }}}

	// #2: Read from memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (rd_mem)
		mem_value <= mem[rd_rdaddr];

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		mem_xpos  <= 0;
		mem_ypos  <= 0;
		mem_eol   <= 0;
		mem_vlast <= 0;
		// }}}
	end else if (rd_mem && rd_vid_flag)
	begin
		// {{{
		mem_xpos  <= rd_xpos;
		mem_ypos  <= rd_ypos;
		mem_eol   <= rd_eol;
		mem_vlast <= rd_vlast;
		// }}}
	end
	// }}}

	// Distribute the results
	// {{{
	// This stage *REALLY* needs a pair of skid buffers to be done
	// properly ...
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		rd_valid <= 1'b0;
	else if (!rd_valid || rd_ready)
		rd_valid <= rd_mem && rd_vid_flag;

	// Skid the video pixel
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!rd_valid || rd_ready)
		rd_src <= rd_mem && rd_vid_flag;
	else
		rd_src <= 1'b0;

	always @(posedge S_AXI_ACLK)
	if (rd_mem && rd_vid_flag)
		rd_alt <= mem_value;

	assign	rd_value = (rd_src) ? mem_value : rd_alt;
	// }}}

	// Skid the copy pixel
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!copy_valid || copy_ready)
		cp_src <= rd_mem && !rd_vid_flag;
	else
		cp_src <= 1'b0;

	always @(posedge S_AXI_ACLK)
	if (rd_mem && !rd_vid_flag)
		cp_alt <= mem_value;

	assign	cp_value = (cp_src) ? mem_value : cp_alt;
	// }}}

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || wr_swap_pages || OPT_FRAMED)
		copy_valid <= 1'b0;
	else if (!copy_valid || copy_ready)
		copy_valid <= rd_mem && !rd_vid_flag && !wr_page_fill[LGMEM-1];

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || OPT_FRAMED)
		copy_addr <= 0;
	else if ((!copy_valid || copy_ready) && rd_mem && !rd_vid_flag)
		copy_addr <= rd_rdaddr[LGMEM-2:0];
	// }}}

	assign	rd_ready = !vs_valid || vs_ready;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #2. vs_*: Take the read value, multiply it by the scale
	// {{{

	//	Signed multiplication
	//
	//	vs_value <= h_val * vs_scale	// IW * LGFRAME bits
	//	vs_eol   <= h_eol
	//

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		vs_valid <= 0;

		vs_xpos  <= 0;
		vs_ypos  <= 0;
		vs_eol   <= 0;
		vs_vlast <= 0;
		// }}}
	end else if (!vs_valid || vs_ready)
	begin
		// {{{
		vs_valid <= rd_valid;

		vs_xpos  <= rd_xpos;
		vs_ypos  <= rd_ypos;
		vs_eol   <= rd_eol;
		vs_vlast <= rd_vlast;
		// }}}
	end // else if (yp_ready)
	//	vs_valid <= 1'b0;

	// vs_value = read value times our vertical scale
	// {{{
	generate if (OPT_UNSIGNED)
	begin
		wire	[LGFRAME:0]	us_scale;
		wire	[IW-1:0]	us_value;
		reg	[LGFRAME+IW:0]	us_product;

		assign	us_scale = { 1'b0, vs_scale };
		assign	us_value = rd_value;

		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN && (!vs_valid || vs_ready))
			us_product <= us_value * us_scale;

		assign	vs_value = us_product[IW + LGFRAME -1 : IW];

		// Verilator lint_off UNUSED
		wire	unused_product;
		assign	unused_product = &{ 1'b0, us_product[IW+LGFRAME], us_product[IW-1:0] };
		// Verilator lint_on  UNUSED
	end else begin
		wire	signed	[LGFRAME:0]	sgn_scale;
		wire	signed	[IW-1:0]	sgn_value;
		reg	signed	[LGFRAME+IW:0]	sgn_product;

		assign	sgn_scale = { 1'b0, vs_scale };
		assign	sgn_value = rd_value;

		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN && (!vs_valid || vs_ready))
			sgn_product <= sgn_value * sgn_scale;

		assign	vs_value = sgn_product[IW + LGFRAME -1 : IW];

		// Verilator lint_off UNUSED
		wire	unused_product;
		assign	unused_product = &{ 1'b0, sgn_product[IW+LGFRAME], sgn_product[IW-1:0] };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}

	// vs_scale tracking
	// {{{
	always @(posedge S_AXI_ACLK)
	if (OPT_UNSIGNED)
		vs_min_goal <= (i_height>>1) + (i_height >> 2);
	else
		vs_min_goal <= (i_height>>2) + (i_height >> 3);

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		vs_scale <= { 3'b001, {(LGFRAME-3){1'b0}} };
	else if (vs_valid && vs_ready && vs_eol && vs_vlast)
	begin
		// $display("YP-MAX: %5d, CLIPPED: %5d, VS-SCALE: %5d", yp_max,
		//	num_clipped, vs_scale);
		if (num_clipped == 0)
		begin
			if (vs_scale < (1<<LGFRAME)-4)
			begin
				if (yp_max < (vs_min_goal >> 2))
					vs_scale <= vs_scale + 4;
				else if (yp_max < (vs_min_goal >> 1))
					vs_scale <= vs_scale + 2;
				else if (yp_max < vs_min_goal)
					vs_scale <= vs_scale + 1;
			end
		end else if (vs_scale > 0
				&& ((!OPT_UNSIGNED && yp_max > i_height/2 - 1)
				  || (OPT_UNSIGNED && yp_max > i_height - 1)))
			vs_scale <= vs_scale - 1;
	end
	// }}}

	assign	vs_ready = !yp_valid || yp_ready;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #3. yp_*: Convert the result to y position
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	//	Nominally, yp_value <= i_height/2 - vs_value;
	//
	//	clipped <= 0;
	//	if (vs_value > i_height/2)
	//	begin
	//		yp_value <= 0;
	//		clipped  <= 1;
	//	end else if (vs_value < -i_height/2)
	//	begin
	//		yp_value <= i_height - 1
	//		clipped  <= 1;
	//	else begin
	//		yp_value <= i_height/2 - vs_value;
	//		clipped  <= 0;
	//	end

	// yp_valid, yp_xpos, yp_ypos, yp_eol, yp_vlast
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		yp_valid <= 1'b0;

		yp_xpos  <= 0;
		yp_ypos  <= 0;
		yp_eol   <= 0;
		yp_vlast <= 0;
		// }}}
	end else if (!yp_valid || yp_ready)
	begin
		// {{{
		yp_valid <= vs_valid;

		yp_xpos  <= vs_xpos;
		yp_ypos  <= vs_ypos;
		yp_eol   <= vs_eol;
		yp_vlast <= vs_vlast;
		// }}}
	end else if (M_VID_READY)
		yp_valid <= 1'b0;

	// yp_sof
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		yp_sof <= 1;
	else if (yp_valid && yp_ready)
		yp_sof <= yp_vlast && yp_eol;
	// }}}

	// vs_posn, vs_abs
	// {{{
	generate if (OPT_UNSIGNED)
	begin

		assign	vs_posn = i_height-1 - vs_value;
		assign	vs_abs =  { 1'b0, vs_value };

	end else begin
		wire	[LGFRAME:0]	vs_neg;

		assign	vs_neg = -{ vs_value[LGFRAME-1], vs_value };
		assign	vs_posn = { 1'b0, i_height }/2 + vs_neg;
		assign	vs_abs = vs_value[LGFRAME-1] ? vs_neg: { 1'b0, vs_value };
	end endgenerate
	// }}}

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		yp_max     <= 0;
		yp_value   <= 0;
		yp_clipped <= 0;
		// }}}
	end else if (vs_valid && vs_ready)
	begin
		// yp_max --- calculate the maximum value per row
		// {{{
		if (vs_valid)
		begin
			if (yp_sof)
				yp_max <=  vs_abs[LGFRAME-1:0];
			else if (vs_abs[LGFRAME-1:0] > yp_max)
				yp_max <=  vs_abs[LGFRAME-1:0];
		end
		// }}}

		// yp_value -- clip any overflow to the maximum value
		// {{{
		if (!OPT_UNSIGNED && vs_posn[LGFRAME:LGFRAME-1] != 2'b00)
		begin
			// Clipped negative, position was to be too low
			yp_value   <= 0;
			yp_clipped <= 1;

			// OPT_UNSIGNED will (should) *never* be negative
		end else if (vs_posn > i_height - 1)
		begin
			// Position was too high
			yp_value   <= i_height - 1;
			yp_clipped <= 1;
		end else begin
			// Just right --- keep it
			yp_value    <= vs_posn[LGFRAME-1:0];
			yp_clipped  <= 0;
		end
		// }}}
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		clip_count    <= 0;
		num_clipped   <= 0;
	end else if (yp_valid && yp_ready)
	begin
		if (yp_eol)
		begin
			clip_count <= 0;
			num_clipped <= clip_count + (yp_clipped ? 1:0);
		end else if (yp_clipped)
			clip_count <= clip_count + 1;
	end

	assign	yp_ready = !M_VID_VALID || M_VID_READY;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #3: M_VID_*: Convert to a pixel value
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_VID_VALID <= 0;
	else if (!M_VID_VALID || M_VID_READY)
		M_VID_VALID <= yp_valid;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_VID_VLAST <= 0;
	else if (!M_VID_VALID || M_VID_READY)
		M_VID_VLAST <= yp_vlast && yp_eol;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_VID_HLAST <= 0;
	else if (!M_VID_VALID || M_VID_READY)
		M_VID_HLAST <= yp_eol;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_VID_SOF <= 1;
	else if (M_VID_VALID && M_VID_READY)
		M_VID_SOF <= M_VID_VLAST;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		m_value <= 0;
	else if (yp_valid && yp_ready)
		m_value <= yp_value;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_VID_DATA <= 0;
	else if (!M_VID_VALID || M_VID_READY)
	begin
		// Unless told otherwise, everything will be in the background
		// color.
		M_VID_DATA <= BACKGROUND_COLOR;

		// Plot a y-axis baseline.  To skip this logic,
		// simply set AXIS_COLOR to BACKGROUND_COLOR
		if (OPT_UNSIGNED)
		begin
			if (yp_vlast)
				M_VID_DATA <= AXIS_COLOR;
		end else begin // if !OPT_UNSIGNED
			if (yp_ypos == i_height/2)
				M_VID_DATA <= AXIS_COLOR;
		end

		if (OPT_LINE)
		begin
			if (yp_ypos == yp_value)
				M_VID_DATA <= LINE_COLOR;
			if (!M_VID_HLAST)
			begin
				if ((yp_ypos >= yp_value && yp_ypos < m_value)
				  ||(yp_ypos <= yp_value && yp_ypos > m_value))
					M_VID_DATA <= LINE_COLOR;
			end
		end else if (yp_ypos == yp_value) // && !OPT_HLINE
			M_VID_DATA <= LINE_COLOR;
	end

	generate if (OPT_TUSER_IS_SOF)
	begin : SOF_FLAGS

		assign	M_VID_LAST = M_VID_HLAST;
		assign	M_VID_USER = M_VID_SOF;

	end else begin : VLAST_FLAGS

		assign	M_VID_LAST = M_VID_VLAST;
		assign	M_VID_USER = M_VID_HLAST;

		// Verilator lint_off UNUSED
		wire	unused_flag = &{ 1'b0, M_VID_SOF, mem_xpos, mem_vlast,
						mem_ypos, mem_eol };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}

	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, yp_xpos, vs_abs[LGFRAME], m_value };
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
	// Local declarations
	// {{{
	reg	f_past_valid;
	wire			f_vlast, f_hlast, f_sof, f_known_height;
	wire	[LGFRAME-1:0]	f_xpos, f_ypos;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Input properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || $past(!S_AXI_ARESETN))
		assume(!S_AXIS_TVALID);
	else if ($past(S_AXIS_TVALID && !S_AXIS_TREADY))
	begin
		assume(S_AXIS_TVALID);
		assume($stable(S_AXIS_TDATA));
		// assume($stable(S_AXIS_TLAST));
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		assume($stable(i_width));
		assume($stable(i_height));

		assume(i_width  > 2);
		assume(i_height > 2);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// RD properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire			frd_hlast, frd_vlast, frd_sof, frd_known_height;
	wire	[LGFRAME-1:0]	frd_xpos, frd_ypos;

	faxivideo #(
		// {{{
		.PW(LGFRAME), .LGDIM(LGFRAME), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) frdvid (
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset_n(S_AXI_ARESETN),
		//
		.S_VID_TVALID(rd_valid), .S_VID_TREADY(rd_ready),
		.S_VID_TDATA(rd_value), .S_VID_TLAST(rd_vlast && rd_eol),
		.S_VID_TUSER(rd_eol),
		//
		.i_width(i_width), .i_height(i_height),
		.o_xpos(frd_xpos), .o_ypos(frd_ypos),
		.f_known_height(frd_known_height),
		.o_hlast(frd_hlast), .o_vlast(frd_vlast), .o_sof(frd_sof)
		// }}}
	);


	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		assert(frd_hlast == rd_eol);
		assert(frd_vlast == rd_vlast);

		assert(frd_xpos == rd_xpos);
		assert(frd_ypos == rd_ypos);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// VS properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire			fvs_hlast, fvs_vlast, fvs_sof, fvs_known_height;
	wire	[LGFRAME-1:0]	fvs_xpos, fvs_ypos;

	faxivideo #(
		// {{{
		.PW(LGFRAME), .LGDIM(LGFRAME), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) fvsvid (
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset_n(S_AXI_ARESETN),
		//
		.S_VID_TVALID(vs_valid), .S_VID_TREADY(vs_ready),
		.S_VID_TDATA(vs_value), .S_VID_TLAST(vs_vlast && vs_eol),
		.S_VID_TUSER(vs_eol),
		//
		.i_width(i_width), .i_height(i_height),
		.o_xpos(fvs_xpos), .o_ypos(fvs_ypos),
		.f_known_height(fvs_known_height),
		.o_hlast(fvs_hlast), .o_vlast(fvs_vlast), .o_sof(fvs_sof)
		// }}}
	);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		assert(fvs_hlast == vs_eol);
		assert(fvs_vlast == vs_vlast);

		assert(fvs_xpos == vs_xpos);
		assert(fvs_ypos == vs_ypos);
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		if (vs_valid)
		begin
			if (fvs_hlast && fvs_vlast)
			begin
				assert(frd_xpos == 0);
				assert(frd_ypos == 0);
			end else if (fvs_hlast)
			begin
				assert(frd_xpos == 0);
				assert(frd_ypos == fvs_ypos + 1);
			end else begin
				assert(frd_xpos == fvs_xpos + 1);
				assert(frd_ypos == fvs_ypos);
			end
		end else begin
			assert(frd_xpos == fvs_xpos);
			assert(frd_ypos == fvs_ypos);
		end
	end


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// YP properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire		fyp_hlast, fyp_vlast, fyp_sof, fyp_known_height;
	wire	[LGFRAME-1:0]	fyp_xpos, fyp_ypos;

	faxivideo #(
		// {{{
		.PW(LGFRAME), .LGDIM(LGFRAME),
		.OPT_TUSER_IS_SOF(1'b0)
		// }}}
	) fypvid (
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset_n(S_AXI_ARESETN),
		//
		.S_VID_TVALID(yp_valid), .S_VID_TREADY(yp_ready),
		.S_VID_TDATA(yp_value), .S_VID_TLAST(yp_vlast && yp_eol),
		.S_VID_TUSER(yp_eol),
		//
		.i_width(i_width), .i_height(i_height),
		.o_xpos(fyp_xpos), .o_ypos(fyp_ypos),
		.f_known_height(fyp_known_height),
		.o_hlast(fyp_hlast), .o_vlast(fyp_vlast), .o_sof(fyp_sof)
		// }}}
	);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		assert(fyp_hlast == yp_eol);
		assert(fyp_sof   == yp_sof);
		assert(fyp_vlast == yp_vlast);

		assert(fyp_xpos == yp_xpos);
		assert(fyp_ypos == yp_ypos);
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		if (yp_valid)
		begin
			if (fyp_hlast && fyp_vlast)
			begin
				assert(fvs_xpos == 0);
				assert(fvs_ypos == 0);
			end else if (fyp_hlast)
			begin
				assert(fvs_xpos == 0);
				assert(fvs_ypos == fyp_ypos + 1);
			end else begin
				assert(fvs_xpos == fyp_xpos + 1);
				assert(fvs_ypos == fyp_ypos);
			end
		end else begin
			assert(fvs_xpos == fyp_xpos);
			assert(fvs_ypos == fyp_ypos);
		end
	end


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxivideo #(
		// {{{
		.PW(PW), .LGDIM(LGFRAME), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) fvid (
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset_n(S_AXI_ARESETN),
		//
		.S_VID_TVALID(M_VID_VALID), .S_VID_TREADY(M_VID_READY),
		.S_VID_TDATA(M_VID_DATA), .S_VID_TLAST(M_VID_LAST),
		.S_VID_TUSER(M_VID_USER),
		//
		.i_width(i_width), .i_height(i_height),
		.o_xpos(f_xpos), .o_ypos(f_ypos),
		.f_known_height(f_known_height),
		.o_hlast(f_hlast), .o_vlast(f_vlast), .o_sof(f_sof)
		// }}}
	);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		if (M_VID_VALID)
		begin
			if (M_VID_HLAST && M_VID_VLAST)
			begin
				assert(fyp_xpos == 0);
				assert(fyp_ypos == 0);
			end else if (M_VID_HLAST)
			begin
				assert(fyp_xpos == 0);
				assert(fyp_ypos == f_ypos + 1);
			end else begin
				assert(fyp_xpos == f_xpos + 1);
				assert(fyp_ypos == f_ypos);
			end
		end else begin
			assert(fyp_xpos == f_xpos);
			assert(fyp_ypos == f_ypos);
		end
	end

	// }}}
`endif
// }}}
endmodule
