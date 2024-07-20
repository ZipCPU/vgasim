////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/gfx/vid_histogram.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Produces a video (AXI) stream output containing a histogram
//		trace.  Data will arrive over the course of a sampling window,
//	up to some maximum amount.  Once that much data have arrived, the
//	histogram accumulation will stop and wait for the end of a frame.  While
//	the histogram is accumulating, a second histogram buffer will be
//	plotted on the screen.  Once the end of the frame arrives, the ping-pong
//	buffers will swap if the accumulation buffer has achieved a full
//	histogram's worth of data.
//
//	Limitations: no engineering units, no cursor, etc.
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
module	vid_histogram #(
		// {{{
		parameter	LGHIST = 10,	// Histogram of 1024 input vals
		parameter	PW = 1,		// Pixel width
		parameter [PW-1:0]	ACTIVE_PIXEL = 1,
		parameter [PW-1:0]	BACKGROUND_PIXEL = 0,
		parameter [PW-1:0]	LINE_PIXEL = 1,
		parameter		LGDIM = 11,	// 10 bits for scrn dim
		parameter		IW = 8,
		parameter		LGMEM = IW+1,
		parameter [0:0]		OPT_SIGNED = 1'b1,
		parameter [0:0]		OPT_LOWPOWER = 1'b0,
		parameter [0:0]		OPT_TUSER_IS_SOF = 1'b1
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK, S_AXI_ARESETN,
		// Input data
		input	wire		S_AXIS_TVALID,
		output	wire		S_AXIS_TREADY,
		input	wire [IW-1:0]	S_AXIS_TDATA,
		// input wire		S_AXIS_TLAST,	// (Unused)
		// input wire		i_trigger,	// (Possibly??)
		//
		// Output video stream
		output	reg		M_VID_VALID,
		input	wire		M_VID_READY,
		output	wire [PW-1:0]	M_VID_DATA,
		output	wire		M_VID_LAST,	// HLAST / VLAST
		output	wire		M_VID_USER,	// SOF   / HLAST
		//
		// Video setup
		input	wire	[LGDIM-1:0]	i_height, i_width
		// }}}
	);

	// Local definitions
	// {{{
	localparam	HEXTRA = 4, VEXTRA = 4;

	reg	[LGHIST:0]	mem	[0:(1<<LGMEM)-1];
	reg			write_bank;
	wire			read_bank;
	reg			swap_banks, clearing_bank, initial_clearing,
				swap_pipe;

	reg	[LGHIST:0]	rd_mem_counts_raw, new_mem_counts, total_counts;
	wire	[LGHIST:0]	rd_mem_counts;
	reg	[LGMEM-1:0]	wr_data_address, rd_mem_addr, new_mem_addr;
	reg			wr_mem, rd_mem_valid;

	///////
	reg				h_valid, vs_valid, th_valid;
	wire				h_ready, vs_ready, th_ready;
	reg				heol, vs_eol, th_eol, px_eof;
	reg	[LGDIM-1:0]		hpos, px_vpos;
	reg	[LGDIM:0]		ovcount, th_overflows;
	reg	[LGHIST:0]		h_data;
	reg	[LGMEM+HEXTRA-1:0]	haddr, hdelta;
	reg	[LGHIST+LGDIM+VEXTRA-1:0]	vs_product;
	reg	[LGDIM+VEXTRA-1:0]		vs_scale;
	wire	[LGDIM-1:0]		vs_value;
	reg	[LGDIM-1:0]		th_value, th_line_max, th_maxvalue;

	reg	[PW-1:0]		px_pixel;

	reg				M_VID_VLAST, M_VID_HLAST;

	reg			bypass_active;
	reg	[LGHIST:0]	bypass_value;
	// }}}
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	// Generate the histogram
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////

	// Clock #1: Read data from memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		rd_mem_valid <= 1;
	else
		rd_mem_valid <= S_AXIS_TVALID && (!clearing_bank && !swap_pipe);

	always @(*)
	if (OPT_SIGNED)
		wr_data_address = { write_bank, !S_AXIS_TDATA[IW-1], S_AXIS_TDATA[IW-2:0] };
	else
		wr_data_address = { write_bank, S_AXIS_TDATA };

	always @(posedge S_AXI_ACLK)
	if (S_AXIS_TVALID)
		rd_mem_counts_raw <= mem[wr_data_address];

	always @(posedge S_AXI_ACLK)
	if (S_AXIS_TVALID)
		rd_mem_addr   <= wr_data_address;
	else
		rd_mem_addr[LGMEM-1] <= write_bank;

	// Bypass--make registered reads act like combinatorial ones
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		bypass_active <= 0;
	else
		bypass_active <= wr_mem
			&& (new_mem_addr == wr_data_address);

	always @(posedge S_AXI_ACLK)
		bypass_value <= new_mem_counts;

	assign	rd_mem_counts = (bypass_active ? bypass_value : rd_mem_counts_raw);
	// }}}

	assign	S_AXIS_TREADY = 1'b1;
	// }}}

	// Clock #2: Increment the counts (also clear memory)
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || swap_banks)
	begin
		// {{{
		wr_mem <= S_AXI_ARESETN && swap_banks;
		new_mem_addr   <= 0;
		if (S_AXI_ARESETN)
			new_mem_addr[LGMEM-1] <= write_bank;
		new_mem_counts <= 0;
		total_counts   <= 0;
		// }}}
	end else if (clearing_bank)
	begin
		// {{{
		wr_mem <= 1;
		if (wr_mem)
			new_mem_addr   <= new_mem_addr + 1;
		if (wr_mem && !initial_clearing)
			new_mem_addr[LGMEM-1] <= write_bank;
		new_mem_counts <= 0;
		total_counts   <= 0;
		// }}}
	end else if (!OPT_LOWPOWER || (rd_mem_valid && !total_counts[LGHIST]))
	begin
		// {{{
		wr_mem <= rd_mem_valid && !total_counts[LGHIST];
		new_mem_addr <= rd_mem_addr;
		if (rd_mem_valid && !total_counts[LGHIST])
			total_counts <= total_counts + 1;
		new_mem_counts <= rd_mem_counts + 1;
		if (wr_mem && new_mem_addr == rd_mem_addr)
			new_mem_counts <= new_mem_counts + 1;
		// }}}
	end else if (OPT_LOWPOWER)
		wr_mem <= 0;
	// }}}

	// Clock #3: Write the new count value back to memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (wr_mem)
		mem[new_mem_addr] <= new_mem_counts;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	// Generate the video
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////

	// 1. h*
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		h_valid <= 0;
	else if (!vs_valid || vs_ready)
		h_valid <= 1'b1;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		hpos   <= 0;
		haddr  <= 0;
		heol   <= 0;
		hdelta <= 0;
	end else if (h_valid && h_ready)
	begin
		heol  <= (hpos == i_width -2);
		hpos  <= hpos + 1;
		if (!haddr[LGMEM+HEXTRA-1])
			haddr <= haddr + hdelta;

		if (heol) // && px_eof
		begin
			hpos  <= 0;

			if (1)
			begin
				// Verilator lint_off WIDTH
				if (haddr[LGMEM+HEXTRA-1])
					hdelta <= hdelta - 1;
				else if ((&hdelta) || (haddr + i_width > (1<<(LGMEM + HEXTRA-1))))
				begin end
				else if (haddr[HEXTRA +: LGMEM] + (i_width<<2) < (1<<(LGMEM-1)))
					hdelta <= hdelta + (4<<HEXTRA);
				else if (haddr[HEXTRA +: LGMEM] + i_width < (1<<(LGMEM-1)))
					hdelta <= hdelta + (1<<HEXTRA);
				else // if (haddr < (1<<(LGMEM + HEXTRA-1)))
					hdelta <= hdelta + 1;
				// Verilator lint_on  WIDTH

				// $display("HADDR: %6d, HDELTA: %5d", haddr, hdelta);
			end

			haddr <= 0;
		end
	end

	always @(posedge S_AXI_ACLK)
	if (!h_valid || h_ready)
		h_data <= mem[ { read_bank, haddr[HEXTRA +: (LGMEM-1)] } ];

	assign	h_ready = !vs_valid || vs_ready;
	// }}}

	// 2. vs_*, the histogram value scaled
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		vs_valid <= 0;
	else if (!vs_valid || vs_ready)
		vs_valid <= h_valid;

`ifdef	FORMAL
	(* anyseq *) wire	[2*LGHIST:0]		f_vs_product;
	always @(posedge S_AXI_ACLK)
	if (!vs_valid || th_ready)
		vs_product <= f_vs_product;
`else
	always @(posedge S_AXI_ACLK)
	if (!vs_valid || th_ready)
		vs_product <= h_data * vs_scale;
`endif

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		vs_eol <= 0;
	else if (!vs_valid || vs_ready)
		vs_eol  <= heol;

	assign	vs_value = (|vs_product[VEXTRA+LGDIM+LGHIST-1:(LGDIM+LGHIST)]) ? -1
					: vs_product[LGHIST +: LGDIM];

	assign	vs_ready = !th_valid || th_ready;
	// }}}

	// 3. th_*, thresholded
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		th_valid <= 0;
	else if (!th_valid || th_ready)
		th_valid <= vs_valid;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		th_eol <= 0;
	else if (!th_valid || th_ready)
		th_eol  <= vs_eol;


	always @(posedge S_AXI_ACLK)
	if (vs_valid && (!th_valid || th_ready))
	begin
		if (vs_eol)
			th_line_max <= 0;
		else if (vs_value >= th_line_max)
			th_line_max <= vs_value;

		if (vs_value >= i_height)
		begin
			th_value <= 0;
			ovcount <= ovcount + 1;
		end else
			th_value <= i_height - 1 - vs_value;
	end

	always @(posedge S_AXI_ACLK)
	if (vs_valid && vs_eol && (!th_valid || th_ready))
	begin
		if (vs_value >= th_line_max)
			th_maxvalue <= vs_value;
		else
			th_maxvalue <= th_line_max;

		if (vs_value >= i_height)
			th_overflows <= ovcount + 1;
		else
			th_overflows <= ovcount;
	end

	//
	// Want to multiply value * (height / max_value)
	//	value * (0.. LGDIM-1) / (0..LGHIST)
	//	Want value == 1 to be able to be mapped to height
	//		So (height / max_value) = (height / 1) = max_height
	//
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		vs_scale <= 4096;
	else if (M_VID_VALID && M_VID_READY && M_VID_VLAST && M_VID_HLAST)
	begin
		if (th_overflows > 0)
			vs_scale <= (vs_scale > 1) ? vs_scale - 1 : vs_scale;
		else if (th_overflows == 0 && !(|vs_scale[LGDIM+VEXTRA-1:2]))
		begin
			if (th_maxvalue < i_height / 8)
				vs_scale <= vs_scale + 4;
			else if (th_maxvalue < i_height / 4)
				vs_scale <= vs_scale + 2;
			else if (th_maxvalue < i_height / 2)
				vs_scale <= vs_scale + 1;
		end

		// $display("VS-SCALE: %4d, H-DELTA: %4d", vs_scale, hdelta);
	end

	assign	th_ready = !M_VID_VALID || M_VID_READY;
	// }}}

	// 4. M_VID_*, the outgoing channel
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		M_VID_VALID <= 1'b0;
		M_VID_HLAST <= 1'b0;
		M_VID_VLAST <= 1'b0;
	end else if (!M_VID_VALID || M_VID_READY)
	begin
		M_VID_VALID <= th_valid;
		M_VID_HLAST <= th_eol;
		M_VID_VLAST <= th_eol && px_eof;
	end

`ifdef	FORMAL
	wire	m_vid_sof;
`endif
	generate if (OPT_TUSER_IS_SOF)
	begin : GEN_M_SOF
		reg	M_VID_SOF;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			M_VID_SOF <= 1'b1;
		else if (M_VID_VALID && M_VID_READY)
			M_VID_SOF <= M_VID_HLAST && M_VID_VLAST;

		assign	M_VID_USER = M_VID_SOF;
		assign	M_VID_LAST = M_VID_HLAST;
`ifdef	FORMAL
		assign	m_vid_sof = M_VID_SOF;
`endif
	end else begin : GEN_M_VLAST
		assign	M_VID_USER = M_VID_HLAST;
		assign	M_VID_LAST = M_VID_VLAST;
`ifdef	FORMAL
		assign	m_vid_sof = 1'b0;
`endif
	end endgenerate

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		px_vpos <= 0;
		px_eof  <= 0;
	end else if (th_valid && (!M_VID_VALID || M_VID_READY))
	begin
		if (th_eol)
		begin
			if (px_eof)
				px_vpos <= 0;
			else
				px_vpos <= px_vpos + 1;

			px_eof <= (px_vpos == i_height - 2);
		end
	end

	always @(posedge S_AXI_ACLK)
	if (th_valid && (!M_VID_VALID || M_VID_READY))
	begin
		if (px_vpos == th_value)
			px_pixel <= LINE_PIXEL;
		else if (px_vpos > th_value)
			px_pixel <= ACTIVE_PIXEL;
		else // if (px_vpos > th_value)
			px_pixel <= BACKGROUND_PIXEL;
	end

	assign	M_VID_DATA = px_pixel;

	//	pxeof <= (vnow >= i_height-1)
	//	eof <= (pxeof && (heol || vs_eol || theol);
	//
	//	if (pxeof && theol)
	//	begin
	//		if (ovflow > 0)
	//			vscale <= vscale - 1;
	//	end
	//

	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Swap memory banks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	read_bank = !write_bank;

	// swap_banks, write_bank, swap_pipe
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		swap_banks <= 0;
		write_bank <= 1;
	end else if (M_VID_VALID && M_VID_READY && M_VID_VLAST
			&& total_counts[LGHIST])
	begin
		swap_banks <= 1'b1;
		if (!swap_banks)
			write_bank <= !write_bank;
	end else if (wr_mem && swap_pipe)
		swap_banks <= 1'b0;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		swap_pipe <= 0;
	else
		swap_pipe <= clearing_bank;
	// }}}

	// initial_clearing, clearing_bank
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		initial_clearing <= 1;
		clearing_bank    <= 1;
	end else if (swap_banks)
	begin
		clearing_bank    <= 1;
		// initial_clearing stays constant
	end else if (clearing_bank && wr_mem && swap_pipe)
	begin
		if (&new_mem_addr[LGMEM-2:1])
		begin
			if (initial_clearing)
			begin
				// clearing_bank <= 1; // Should still be 1
				if (new_mem_addr[0])
					initial_clearing <= 1'b0;
			end else
				clearing_bank <= 0;
		end
	end
	// }}}

	// }}}
	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, vs_product };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal methods
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Local declarations
	// {{{
	reg			f_past_valid;
	wire			fh_hlast, fh_vlast, fh_sof, fh_known_height;
	wire	[LGDIM-1:0]	fh_xpos, fh_ypos;
	wire			fvs_hlast, fvs_vlast, fvs_sof, fvs_known_height;
	wire	[LGDIM-1:0]	fvs_xpos, fvs_ypos;
	wire			fth_hlast, fth_vlast, fth_sof, fth_known_height;
	wire	[LGDIM-1:0]	fth_xpos, fth_ypos;
	wire			f_hlast, f_vlast, f_sof, f_known_height;
	wire	[LGDIM-1:0]	f_xpos, f_ypos;

	(* anyconst *)	reg [LGMEM-1:0]	fc_addr;
	wire	[LGHIST:0]	f_data;
	reg	[LGHIST:0]	f_counts;


	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Input stream assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		assume($stable(i_width));
		assume($stable(i_height));

		assume(i_width  > 2);
		assume(i_height > 2);
	end


	always @(posedge S_AXI_ACLK)
	if (!f_past_valid)
	begin end else if ($past(!S_AXI_ARESETN))
	begin
		assume(!S_AXIS_TVALID);
	end else if ($past(S_AXIS_TVALID && !S_AXIS_TREADY))
	begin
		assume(S_AXIS_TVALID);
		assume($stable(S_AXIS_TDATA));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing video stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxivideo #(
		// {{{
		.PW(PW), .LGDIM(LGDIM), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
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
			if (f_hlast)
			begin
				assert(fth_xpos == 0);
				if (f_vlast)
				begin
					assert(fth_ypos == 0);
				end else
					assert(f_ypos + 1 == fth_ypos);
			end else begin
				assert(f_xpos + 1 == fth_xpos);
				assert(f_ypos == fth_ypos);
			end
		end else begin
			assert(f_xpos == fth_xpos);
			assert(f_ypos == fth_ypos);
		end

		assert(M_VID_HLAST == f_hlast);
		assert(M_VID_VLAST == (f_vlast && f_hlast));
		if (OPT_TUSER_IS_SOF)
			assert(m_vid_sof == (f_xpos == 0 && f_ypos == 0));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Internal h* video stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxivideo #(
		// {{{
		.PW(PW), .LGDIM(LGDIM), .OPT_TUSER_IS_SOF(1'b0)
		// }}}
	) fvid_h (
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset_n(S_AXI_ARESETN),
		//
		.S_VID_TVALID(h_valid), .S_VID_TREADY(h_ready),
		.S_VID_TDATA(haddr), .S_VID_TLAST(heol&& fh_ypos == i_height-1),
		.S_VID_TUSER(heol),
		//
		.i_width(i_width), .i_height(i_height),
		.o_xpos(fh_xpos), .o_ypos(fh_ypos),
		.f_known_height(fh_known_height),
		.o_hlast(fh_hlast), .o_vlast(fh_vlast), .o_sof(fh_sof)
		// }}}
	);

	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(fh_xpos == hpos);
		assert(fh_hlast == heol);
	end


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Internal vs_* (vertical scale) video stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxivideo #(
		// {{{
		.PW(PW), .LGDIM(LGDIM), .OPT_TUSER_IS_SOF(1'b0)
		// }}}
	) fvid_vs (
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset_n(S_AXI_ARESETN),
		//
		.S_VID_TVALID(vs_valid), .S_VID_TREADY(vs_ready),
		.S_VID_TDATA(vs_product),
				.S_VID_TLAST(vs_eol&& fvs_ypos == i_height-1),
		.S_VID_TUSER(vs_eol),
		//
		.i_width(i_width), .i_height(i_height),
		.o_xpos(fvs_xpos), .o_ypos(fvs_ypos),
		.f_known_height(fvs_known_height),
		.o_hlast(fvs_hlast), .o_vlast(fvs_vlast), .o_sof(fvs_sof)
		// }}}
	);

	always @(*)
	if (S_AXI_ARESETN)
		assert(vs_eol == fvs_hlast);

	always @(*)
	if (S_AXI_ARESETN && vs_valid)
	begin
		if (vs_eol)
			assert(hpos == 0);
		else
			assert(hpos == fvs_xpos + 1);
	end else if (S_AXI_ARESETN)
		assert(hpos == fvs_xpos);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Internal th_* (threshold stage) video stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxivideo #(
		// {{{
		.PW(PW), .LGDIM(LGDIM), .OPT_TUSER_IS_SOF(1'b0)
		// }}}
	) fvid_th (
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset_n(S_AXI_ARESETN),
		//
		.S_VID_TVALID(th_valid), .S_VID_TREADY(th_ready),
		.S_VID_TDATA(th_value),
				.S_VID_TLAST(th_eol&& fth_ypos == i_height-1),
		.S_VID_TUSER(th_eol),
		//
		.i_width(i_width), .i_height(i_height),
		.o_xpos(fth_xpos), .o_ypos(fth_ypos),
		.f_known_height(fth_known_height),
		.o_hlast(fth_hlast), .o_vlast(fth_vlast), .o_sof(fth_sof)
		// }}}
	);

	always @(*)
	if (S_AXI_ARESETN)
		assert(th_eol == fth_hlast);

	always @(*)
	if (S_AXI_ARESETN && th_valid)
	begin
		if (th_eol)
			assert(fvs_xpos == 0);
		else
			assert(fvs_xpos == fth_xpos + 1);
	end else if (S_AXI_ARESETN)
		assert(fvs_xpos == fth_xpos);

	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(px_eof   == fth_vlast);
		assert(px_vpos  == fth_ypos);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Histogram contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	f_data = mem[fc_addr];

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && initial_clearing)
		assert(clearing_bank);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $fell(initial_clearing || clearing_bank)
				&& new_mem_addr[LGMEM-1] == fc_addr[LGMEM-1])
	begin
		if (wr_mem && new_mem_addr == fc_addr)
		begin
			// Might still be writing a last value
			assert(new_mem_counts == 0);
		end else
			assert(f_data == 0);
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !$past(S_AXI_ARESETN))
	begin end
	else if (f_past_valid && initial_clearing && !fc_addr[LGMEM-1])
	begin
		assert(!new_mem_addr[LGMEM-1]);
		if (new_mem_addr[LGMEM-2:0] > fc_addr[LGMEM-2:0])
			assert(f_data == 0);
	end else if (clearing_bank && fc_addr[LGMEM-1] == new_mem_addr[LGMEM-1])
	begin
		if (new_mem_addr[LGMEM-2:0] > fc_addr[LGMEM-2:0])
			assert(f_data == 0);
	end

	always @(*)
	if (S_AXI_ARESETN && clearing_bank)
		assert(wr_mem || new_mem_addr == 0);

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || ((initial_clearing || clearing_bank)
				&& new_mem_addr[LGMEM-1] == fc_addr[LGMEM-1]))
		f_counts <= 0;
	else if (!total_counts[LGHIST]
			&& rd_mem_valid && rd_mem_addr == fc_addr)
		f_counts <= f_counts + 1;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin end
	else if (clearing_bank)
	begin
		if (!swap_banks)
		casez({ initial_clearing, new_mem_addr[LGMEM-1],
			fc_addr[LGMEM-1],
			((new_mem_addr[LGMEM-2]>fc_addr[LGMEM-2])? 1'b1:1'b0) })
		4'b0000: assert(f_counts == 0);
		4'b0001: assert(f_counts == 0 && f_data == 0);
		4'b001?: assert(f_counts == f_data);
		4'b010?: assert(f_counts == f_data);
		4'b0110: begin end // assert(f_counts == 0);
		4'b0111: assert(f_counts == 0 && f_data == 0);
		//
		4'b1000: assert(f_counts == 0);
		4'b1001: assert(f_counts == 0 && f_data == 0);
		4'b101?: begin end
		4'b11??: assert(0);
		endcase
	end else if (wr_mem && new_mem_addr == fc_addr)
	begin
		assert(new_mem_counts == f_counts);
	end else if (write_bank == fc_addr[LGMEM-1]
			&& (!swap_banks || clearing_bank))
	begin
		assert(f_counts == f_data);
	end

	always @(*)
	if (S_AXI_ARESETN && initial_clearing)
		assert(write_bank);

	always @(*)
	if (S_AXI_ARESETN && !initial_clearing && !swap_banks)
		assert(write_bank == new_mem_addr[LGMEM-1]);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && write_bank == fc_addr[LGMEM-1]
				&& !swap_banks && !clearing_bank)
		assert(f_counts <= total_counts);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
		assert(total_counts <= (1<<LGHIST));
	// }}}
`endif
// }}}
endmodule
