////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axisvoverlay.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Overlay a second video stream on top of a first one, producing
//		an outgoing video stream.
//
// Inputs:
//	Primary video:
//		Can be from a camera or a memory/frame buffer driving a display.
//		The assumption is made that the speed can be controlled by
//		the downstream/output video port.  (i.e., hold READY high if
//		this is coming from a camera, or toggle it if/when the outgoing
//		display is/isn't ready.)
//	Secondary (overlay) video
//		May or may not be present.  Must be able to handle stalls, so
//		must be driven from memory.  The primary video and associated
//		output interface drives drive the speed of the interface.
//		The design will report an error if the secondary video ever
//		gets out of sync.
//
// Outputs:
//	Outgoing AXI Stream video stream
//		To be produced at all costs.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2021-2022, Gisselquist Technology, LLC
// {{{
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
//
//	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module	axisvoverlay #(
		// {{{
		// LGFRAME: Control the number of bits required in the two
		// {{{
		// position counters.  If there will never be more than 2047
		// horizontal positions, then this number never need be more
		// than 11.
		parameter	LGFRAME = 11,
		// }}}
		// ALPHA_BITS: Number of alpha bits in the overlay channel
		// {{{
		// If zero, the overlay will always replace the primary when
		// present.  If one, then the overlay will only replace the
		// primary when the alpha bit is 1.  If greater than 1, then
		// the alpha bits are used to scale both primary, by 1-alpha,
		// and overlay, by alpha, before summing the two together.
		// This allows the generation of a gradient effect if desired.
		parameter	ALPHA_BITS = 1,
		// }}}
		// COLORS: Number of color components to apply alpha mixing to
		// {{{
		// While you might think of this as nominally 3, REG+GRN+BLU,
		// it could be set to 6 (RGB, RGB), or even 9 (RGB, RGB, RGB),
		// if you want to share alpha across multiple pixels.
		parameter	COLORS = 3,
		// }}}
		// BITS_PER_PIXEL: Bits per color component
		// {{{
		parameter	BITS_PER_PIXEL = 8,
		localparam	BPP = BITS_PER_PIXEL,
		parameter	DATA_WIDTH = COLORS * BITS_PER_PIXEL,
		localparam	DW = DATA_WIDTH,
		// }}}
		// OPT_TUSER_IS_SOF: This is the normal video mode, as defined
		// {{{
		// by Xilinx's documentation.  TUSER = the start of frame
		// signal.  This makes TUSER true for the one pixel when
		// X = Y == 0.  TLAST is then used to reference the last item
		// in a line.  Set this to 1 for best compatibility with other
		// video cores for this reason.  Unfortunately, this makes
		// our processing below more challenging.  Therefore, I offer
		// another option: TLAST == the last pixel in the frame, when
		// X == WIDTH -1 && Y == HEIGHT-1.  This is easier to work with
		// internally, and requires less logic.  Both are tested.
		parameter [0:0]	OPT_TUSER_IS_SOF = 1'b1,
		// }}}
		// OPT_LINE_BREAK: If set, then we force READY to be low for
		// {{{
		// one clock cycle following every line break (HLAST).  This
		// allows our pointers to recover and the in_overlay flag to
		// be calculated with seven fewer logic operations on the
		// critical path between clock ticks.  This should help the
		// design pass timing in a high speed environment.
		parameter [0:0]	OPT_LINE_BREAK = 1'b0
		// }}}
		// }}}
	) (
		// {{{
		input	wire	ACLK, ARESETN,
		// Config inputs
		// {{{
		// i_enable: if true, apply the overlay to the primary channel
		// {{{
		input	wire		i_enable,
		// }}}
		// i_hpos, i_vpos: Describe the location of the top-left corner
		// {{{
		// of the overlay.  This will allow the overlay position to be
		// adjusted as necessary.  The design (currently) does not
		// allow the overlay to be positioned partially off screen to
		// either top or left, although running off screen to right or
		// bottom should be okay as long as there's enough bandwidth
		// to allow it.
		input	wire	[LGFRAME-1:0]	i_hpos, i_vpos,
		// }}}
		output	wire		o_err,
		// }}}
		// Primary video input
		// {{{
		input	wire			S_PRI_TVALID,
		output	wire			S_PRI_TREADY,
		input	wire	[DW-1:0]	S_PRI_TDATA,
		input	wire			S_PRI_TLAST,	// HLAST
		input	wire			S_PRI_TUSER,	// SOF
		// }}}
		// Secondary (overlap) video input
		// {{{
		input	wire			S_OVW_TVALID,
		output	wire			S_OVW_TREADY,
		input wire [DW+ALPHA_BITS-1:0]	S_OVW_TDATA,
		input	wire			S_OVW_TLAST,	// HLAST
		input	wire			S_OVW_TUSER,	// SOF
		// }}}
		// Video output
		// {{{
		output	reg			M_VID_TVALID,
		input	wire			M_VID_TREADY,
		output	reg	[DW-1:0]	M_VID_TDATA,
		output	reg			M_VID_TLAST,	// HLAST
		output	reg			M_VID_TUSER	// SOF
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam [ALPHA_BITS:0]	OPAQUE = (1<<ALPHA_BITS),
					TRANSPARENT = 0;

	wire			pskd_tuser, pskd_tlast, pskd_ready, pskd_valid,
				pskd_vlast, pskd_hlast, pskd_sof;
	wire	[DW-1:0]	pskd_data;

	wire			ovskd_tuser, ovskd_tlast, ovskd_ready,
				ovskd_vlast, ovskd_hlast, ovskd_sof,
				ovskd_valid;
	wire [ALPHA_BITS+DW-1:0]	ovskd_data;
	reg			pix_line_pause, ov_line_pause;

	reg	[LGFRAME-1:0]	prhpos, prvpos;
	reg	[LGFRAME-1:0]	ovhpos, ovvpos;
	wire	[LGFRAME-1:0]	lines_per_frame;

	reg	in_overlay, frame_err, ovw_eof, ovw_eol;

	wire	pix_loaded;
	wire	pix_ready;

	wire	mpy_loaded, mpy_ready;
	wire	mix_valid, mix_ready, mix_hlast, mix_vlast, mix_sof;

	wire	[DW-1:0]	mix_pixel;
`ifdef	FORMAL
	(* anyconst *)	reg	[LGFRAME-1:0]	f_vid_width, f_vid_height;
	(* anyconst *)	reg	[LGFRAME-1:0]	f_ovw_width, f_ovw_height;
	reg	[LGFRAME-1:0]	f_pri_hpos, f_pri_vpos;
	reg	[LGFRAME-1:0]	f_ovw_hpos, f_ovw_vpos;
	reg	[LGFRAME-1:0]	f_vid_hpos, f_vid_vpos;
	reg	[LGFRAME-1:0]	f_pskd_hpos, f_pskd_vpos;
	reg	[LGFRAME-1:0]	f_mix_hpos, f_mix_vpos;
	reg		f_pri_known, f_ovw_known;
`endif
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Pixel skid buffers
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	skidbuffer #(
		.DW(DW+2), .OPT_OUTREG(0)
`ifdef	FORMAL
		, .OPT_PASSTHROUGH(1)
`endif
	) primary_skid (
		// {{{
		.i_clk(ACLK), .i_reset(!ARESETN),
		.i_valid(S_PRI_TVALID), .o_ready(S_PRI_TREADY),
			.i_data({ S_PRI_TDATA, S_PRI_TLAST, S_PRI_TUSER }),
		.o_valid(pskd_valid), .i_ready(pskd_ready),
			.o_data({ pskd_data, pskd_tlast, pskd_tuser })
		// }}}
	);

	skidbuffer #(
		.DW(DW+ALPHA_BITS+2), .OPT_OUTREG(0)
`ifdef	FORMAL
		, .OPT_PASSTHROUGH(1)
`endif
	) overlay_skid (
		// {{{
		.i_clk(ACLK), .i_reset(!ARESETN),
		.i_valid(S_OVW_TVALID), .o_ready(S_OVW_TREADY),
			.i_data({ S_OVW_TDATA, S_OVW_TLAST, S_OVW_TUSER }),
		.o_valid(ovskd_valid), .i_ready(ovskd_ready),
			.o_data({ ovskd_data, ovskd_tlast, ovskd_tuser })
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming frame counters, VLAST/SOF insertion
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// VLAST, HLAST, SOF
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin : GEN_VLAST
		// {{{
		reg	p_vlast, ov_vlast;
		reg	[LGFRAME-1:0]	ovw_lines, vcount, ovcount, r_lines;

		assign	pskd_sof   = pskd_tuser;
		assign	pskd_hlast = pskd_tlast;
		assign	pskd_vlast = p_vlast && pskd_hlast;
		assign	lines_per_frame = r_lines;

		// vcount, lines_per_frame, p_vlast
		// {{{
		always @(posedge ACLK)
		if (!ARESETN)
		begin
			p_vlast <= 0;
			vcount  <= 0;
			r_lines <= 0;
		end else if (pskd_valid && pskd_ready)
		begin
			if (pskd_sof)
			begin
				r_lines <= vcount;
				vcount <= 0;
			end

			if (pskd_hlast)
			begin
				vcount <= vcount + 1;
				p_vlast <= (vcount == lines_per_frame - 2);
				if (lines_per_frame == 0)
					p_vlast <= 0;
			end
		end
		// }}}

		assign	ovskd_sof   = ovskd_tuser;
		assign	ovskd_hlast = ovskd_tlast;
		assign	ovskd_vlast = ov_vlast && ovskd_hlast;

		// ovcount, ovw_lines, ovskd_vlast
		// {{{
		always @(posedge ACLK)
		if (!ARESETN)
		begin
			ov_vlast <= 0;
			ovcount     <= 0;
			ovw_lines   <= 0;
		end else if (ovskd_valid && ovskd_ready)
		begin
			if (ovskd_sof)
			begin
				ovw_lines <= ovcount;
				ovcount <= 0;
			end

			if (ovskd_hlast)
			begin
				ovcount <= ovcount + 1;
				ov_vlast <= (ovcount == ovw_lines -2);
			end
		end
		// }}}
`ifdef	FORMAL
		// {{{
		always @(*)
		begin
			f_pri_known = (r_lines == f_vid_height);
			f_ovw_known = (ovw_lines == f_ovw_height);
		end

		always @(*)
		if (ARESETN)
		begin
			assert((r_lines == 0) || (r_lines == f_vid_height));
			if (vcount < f_vid_height)
			begin
				assert(f_pri_vpos == vcount);
				if (r_lines == 0)
				begin
					assert(!p_vlast);
					assert(!f_pri_known);
				end else begin
					assert(f_pri_known);
					assert(p_vlast == (f_pri_vpos == f_vid_height-1));
					assert(f_pskd_vpos != 0 || f_pskd_hpos != 0);
				end
			end else begin
				assert(vcount == f_vid_height);
				assert(!p_vlast);
				assert(f_pri_vpos == 0 && f_pri_hpos == 0);
			end
		end

		always @(*)
		if (ARESETN)
		begin
			if (ovw_lines != 0)
				assert(ovw_lines == f_ovw_height);
			assert((ovw_lines == 0) || (ovw_lines == f_ovw_height));
			if (f_ovw_known)
				assert(ov_vlast == (f_ovw_vpos == f_ovw_height-1));
			if (ovcount < f_ovw_height)
			begin
				assert(f_ovw_vpos == ovcount);
				if (ovw_lines == 0)
				begin
					assert(!f_ovw_known);
					assert(!ov_vlast);
				end else begin
					assert(f_ovw_known);
					assert(ov_vlast == (f_ovw_vpos == f_ovw_height-1));
					assert(f_ovw_vpos != 0 || f_ovw_hpos != 0);
				end
			end else begin
				assert(ovcount == f_ovw_height);
				assert(!ov_vlast);
				assert(f_ovw_vpos == 0 && f_ovw_hpos == 0);
			end
		end
		// }}}
`endif
		// }}}
	end else begin : GEN_SOF
		// {{{
		reg			p_sof, ov_sof;

		assign	pskd_vlast = pskd_tlast && pskd_tuser;
		assign	pskd_hlast = pskd_tuser;
		assign	pskd_sof   = p_sof;
		assign	lines_per_frame = 0;	// A dummy value

		// p_sof
		// {{{
		always @(posedge ACLK)
		if (!ARESETN)
			p_sof <= 1;
		else if (pskd_valid && pskd_ready)
			p_sof <= pskd_tlast && pskd_tuser;
		// }}}

		assign	ovskd_vlast = ovskd_tlast && ovskd_tuser;
		assign	ovskd_hlast = ovskd_tuser;
		assign	ovskd_sof   = ov_sof;

		// ov_sof
		// {{{
		always @(posedge ACLK)
		if (!ARESETN)
			ov_sof <= 1;
		else if (ovskd_valid && ovskd_ready)
			ov_sof <= ovskd_tlast && ovskd_tuser;
		// }}}
`ifdef	FORMAL
		always @(*)
		begin
			f_pri_known = 1;
			f_ovw_known = 1;

			if (ARESETN)
			begin
			assert(pskd_sof == ((f_pri_hpos == 0) && (f_pri_vpos  == 0)));
			assert(ovskd_sof == ((f_ovw_hpos == 0) && (f_ovw_vpos  == 0)));
			end
		end
`endif
		// }}}
	end endgenerate
	// }}}

	// prhpos, prvpos
	//  {{{
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		prhpos <= 0;
		prvpos <= 0;
	end else if (pskd_valid && pskd_ready)
	begin
		if (pskd_hlast)
		begin
			prhpos <= 0;
			prvpos <= prvpos + 1;
			if (pskd_vlast)
				prvpos <= 0;
		end else
			prhpos <= prhpos + 1;

		if (pskd_sof)
			prvpos <= 0;
	end
`ifdef	FORMAL
	always @(*)
	if (ARESETN)
	begin
		assert(prhpos == f_pskd_hpos);
		if (f_pri_known)
			assert(f_pskd_vpos == prvpos);
		if (prvpos < f_vid_height)
		begin
			assert(prvpos == f_pskd_vpos);
		end else if (prvpos != f_pskd_vpos)
		begin
			assert(!f_pri_known);
			assert(prvpos == f_vid_height);
			assert(f_pskd_vpos == 0);
			assert(prhpos == 0);
		end
	end
`endif
	// }}}

	// ovhpos, ovvpos
	//  {{{
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		ovhpos <= 0;
		ovvpos <= 0;
	end else if (ovskd_valid && ovskd_ready)
	begin
		if (ovskd_sof)
			ovvpos <= 0;
		if (ovskd_hlast)
		begin
			ovhpos <= 0;
			ovvpos <= ovvpos + 1;
			if (ovskd_vlast)
				ovvpos <= 0;
		end else
			ovhpos <= ovhpos + 1;
	end
`ifdef	FORMAL
	// {{{
	always @(*)
	if (ARESETN)
	begin
		assert(ovhpos == f_ovw_hpos);
		assert(ovvpos == f_ovw_vpos
			|| (ovvpos == f_ovw_height && f_ovw_hpos == 0
				&& f_ovw_vpos == 0 && !f_ovw_known));
		if (ovskd_valid)
			assert(ovskd_hlast == (f_ovw_hpos == f_ovw_width-1));
	end
	// }}}
`endif
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) line breaks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge ACLK)
	if (!ARESETN || !OPT_LINE_BREAK)
		pix_line_pause <= 1'b0;
	else
		pix_line_pause <= pskd_valid && pskd_ready && pskd_hlast;

	always @(posedge ACLK)
	if (!ARESETN || !OPT_LINE_BREAK)
		ov_line_pause <= 1'b0;
	else
		ov_line_pause <= ovskd_valid && ovskd_ready && ovskd_hlast;

`ifdef	FORMAL
	always @(*)
	if (ARESETN)
	begin
		if (!OPT_LINE_BREAK || f_pskd_hpos != 0)
			assert(!pix_line_pause);
		if (!OPT_LINE_BREAK || f_ovw_hpos != 0)
			assert(!ov_line_pause);
	end
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Overlay flags
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// ovw_eof, ovw_eol
	// {{{
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		ovw_eof    <= 1;
		ovw_eol    <= 1;
	end else if (ovskd_valid && ovskd_ready)
	begin
		ovw_eol <= ovskd_hlast;
		ovw_eof <= ovskd_hlast && ovskd_vlast;
	end
`ifdef	FORMAL
	always @(*)
	if (ARESETN)
	begin
		assert(ovw_eol == (f_ovw_hpos == 0));
		if (f_ovw_known)
			assert(ovw_eof == (f_ovw_vpos == 0 && f_ovw_hpos == 0));
	end
`endif
	// }}}

	// in_overlay
	// {{{
	always @(posedge ACLK)
	if (!ARESETN)
		in_overlay <= 0;
	else if (OPT_LINE_BREAK)
	begin
		in_overlay <= ({ 1'b0, i_hpos} + { 1'b0, ovhpos}
				+ ((ovskd_valid && ovskd_ready)? 1:0)
				== { 1'b0, prhpos}
					+ ((pskd_valid && pskd_ready)? 1:0))
			&& ({ 1'b0, i_vpos} + { 1'b0, ovvpos}
				== { 1'b0, prvpos});
		if (ovskd_valid && ovskd_ready && ovskd_hlast)
			in_overlay <= 1'b0;
	end else casez( {(pskd_valid && pskd_ready && pskd_hlast),		// Primary, end of line
			(pskd_valid && pskd_ready && pskd_vlast),	// Primary, end of frame
			(ovskd_valid && ovskd_ready && ovskd_hlast),	// Overlay, end of line
			(ovskd_valid && ovskd_ready && ovskd_vlast) })	// Overlay, end of frame
	4'b0000: in_overlay <= ({ 1'b0, i_hpos} + { 1'b0, ovhpos} + ((ovskd_valid && ovskd_ready)? 1:0)
					== { 1'b0, prhpos} + ((pskd_valid && pskd_ready)? 1:0))
			&& ({ 1'b0, i_vpos} + { 1'b0, ovvpos} == { 1'b0, prvpos});
	4'b00?1: in_overlay <= ({ 1'b0, i_hpos } == { 1'b0, prhpos } + ((pskd_valid && pskd_ready) ? 1:0))
				&& (i_vpos == prvpos);
	4'b0010: in_overlay <= ({ 1'b0, i_hpos } == { 1'b0, prhpos } + ((pskd_valid && pskd_ready) ? 1:0))
			&& ({ 1'b0, i_vpos } + { 1'b0, ovvpos } + 1 == { 1'b0, prvpos });
	4'b1000: in_overlay <= ({ 1'b0, i_hpos } + { 1'b0, ovhpos }
				+ ((ovskd_valid && ovskd_ready) ? 1:0) == 0)
			&& ({ 1'b0, i_vpos } + { 1'b0, ovvpos } == { 1'b0, prvpos } + 1);
	4'b?100: in_overlay <= ({ 1'b0, i_hpos } + { 1'b0, ovhpos } + ((ovskd_valid && ovskd_ready) ? 1:0)
				== 0) && (i_vpos == 0) && (ovvpos == 0);
	4'b1010: in_overlay <= (i_hpos == 0)
			&& ({ 1'b0, i_vpos } + { 1'b0, ovvpos } == { 1'b0, prvpos });
	4'b?1?1: in_overlay <= (i_hpos == 0)&& (i_vpos == 0);
	//
	// 4'b?110: in_overlay <= 0;	// 6, e
	// 4'b10?1: in_overlay <= 0;	// 9, b
	default: in_overlay <= 1'b0;
	endcase
`ifdef	FORMAL
	// {{{
	always @(posedge ACLK)
	if (ARESETN && (!OPT_LINE_BREAK || pskd_ready))
	begin
		if ({ 1'b0, i_hpos } + { 1'b0, f_ovw_hpos } != { 1'b0, f_pri_hpos })
			assert(!in_overlay);	// !!!
		else if (({ 1'b0, i_vpos } + { 1'b0, ovvpos } != prvpos)
				&& (f_pri_known && $past(f_pri_known))
				&& (f_ovw_known && $past(f_ovw_known))
				) // && prhpos != 1 && ovhpos != 1)
			assert(!in_overlay);
	end
	// }}}
`endif
	// }}}

	// o_err, frame_err
	// {{{
	always @(posedge ACLK)
	if (!ARESETN || !i_enable)
	begin
		frame_err <= 0;
	end else if (!frame_err && pskd_valid && pskd_ready)
	begin
		if (in_overlay)
			frame_err <= (!ovskd_valid || !ovskd_ready);
		else begin
			if (prhpos >= i_hpos && !ovw_eol)
				frame_err <= 1;
			if (prvpos >= i_vpos && !ovw_eof)
				frame_err <= 1;
		end
	end else if (ovskd_valid && ovskd_ready && ovskd_vlast && ovskd_hlast)
	begin
		frame_err <= 0;
	end

	assign	o_err = frame_err;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Mix the two channels together
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// mix_pixel
	// {{{
	generate if (ALPHA_BITS == 0)
	begin : NO_ALPHA
		// {{{
		reg	[DW-1:0]	r_mix_pixel;

		always @(posedge ACLK)
		if (pskd_valid && pskd_ready)
		begin
			r_mix_pixel <= pskd_data;
			if (in_overlay && ovskd_valid && !frame_err)
				r_mix_pixel <= ovskd_data;
		end

		assign	mix_pixel = r_mix_pixel;
		// }}}
	end else if (ALPHA_BITS == 1)
	begin: ALPHA_MASK
		// {{{
		reg	[DW-1:0]	r_mix_pixel;

		always @(posedge ACLK)
		if (pskd_valid && pskd_ready)
		begin
			r_mix_pixel <= pskd_data;
			if (in_overlay && ovskd_valid
					&& !frame_err && ovskd_data[DW])
				r_mix_pixel <= ovskd_data[DW-1:0];
		end

		assign	mix_pixel = r_mix_pixel;
		// }}}
	end else begin : ALPHA_MIXING
		// {{{
		genvar	clr;
		reg	[ALPHA_BITS:0]	alpha, negalpha;
		reg	[DW-1:0]	pri_pixel, ovw_pixel;

		// pri_pixel, ovw_pixel
		// {{{
		always @(posedge ACLK)
		if (!ARESETN)
		begin
			pri_pixel <= 0;
			ovw_pixel <= 0;
			alpha     <= TRANSPARENT;
		end else if (pskd_valid && pskd_ready)
		begin
			pri_pixel <= pskd_data;
			ovw_pixel <= ovskd_data[DW-1:0];
			alpha     <= ovskd_data[ALPHA_BITS + DW-1 : DW]
					+ ovskd_data[ALPHA_BITS + DW-1];
			negalpha  <= (1<<ALPHA_BITS)
					- ovskd_data[ALPHA_BITS + DW-1 : DW]
					- ovskd_data[ALPHA_BITS + DW-1];
			if (!ovskd_valid || frame_err || !in_overlay
							|| !i_enable)
			begin
				ovw_pixel <= 0;
				alpha     <= TRANSPARENT;
			end
		end
		// }}}

		// mix_pixel
		// {{{
		for(clr=0; clr<COLORS; clr=clr+1)
		begin
			reg	[BPP + ALPHA_BITS -1:0] pclr, oclr, sclr;

			always @(posedge ACLK)
			if (pix_loaded && pix_ready)
				pclr <= pri_pixel[clr * BPP +: BPP] * negalpha;

			always @(posedge ACLK)
			if (pix_loaded && pix_ready)
				oclr <= ovw_pixel[clr * BPP +: BPP] * alpha;

			always @(posedge ACLK)
			if (mpy_loaded && mpy_ready)
				sclr <= pclr[clr] + oclr[clr];

			assign	mix_pixel[clr * BPP +: BPP] = sclr;
		end
		// }}}
		// }}}
	end endgenerate
	// }}}

	// mix_hlast, mix_vlast, mix_sof
	// {{{
	generate if (ALPHA_BITS <= 1)
	begin : NO_ALPHA_PIPELINE
		reg	r_mix_sof, r_mix_valid, r_mix_hlast, r_mix_vlast;

		assign	pskd_ready = !pix_line_pause
				&&(!mix_valid || !M_VID_TVALID || M_VID_TREADY);
		// {{{
		initial	r_mix_valid = 0;
		always @(posedge ACLK)
		if (!ARESETN)
			r_mix_valid <= 1'b0;
		else if (pskd_valid && pskd_ready)
			r_mix_valid <= 1'b1;
		else if (mix_ready)
			r_mix_valid <= 1'b0;

		always @(posedge ACLK)
		if (pskd_valid && pskd_ready)
		begin
			r_mix_hlast <= pskd_hlast;
			r_mix_vlast <= pskd_vlast;
			r_mix_sof   <= pskd_sof;
		end

		assign	mix_valid = r_mix_valid;
		assign	mix_hlast = r_mix_hlast;
		assign	mix_vlast = r_mix_vlast;
		assign	mix_sof   = r_mix_sof;

		assign	mix_ready = !M_VID_TVALID || M_VID_TREADY;
		// }}}

		// Keep Verilator happy
		// {{{
		wire	unused_no_alpha;
		assign	pix_ready = 1'b0;
		assign	{ pix_loaded, mpy_loaded, mpy_ready } = 0;
		assign	unused_no_alpha = &{ 1'b0, pix_loaded, mpy_loaded,
				pix_ready, mix_valid, mpy_ready, mix_ready };
		// }}}
`ifdef	FORMAL
		always @(*)
		if (ARESETN)
		begin
			if (!mix_valid)
			begin
				assert(f_pskd_hpos == f_mix_hpos);
				assert(f_pskd_vpos == f_mix_vpos);
			end else if (f_mix_hpos < f_vid_width-1)
			begin
				assert(f_pskd_hpos == f_mix_hpos + 1);
				assert(f_pskd_vpos == f_mix_vpos);
			end else if (f_mix_vpos < f_vid_height-1)
			begin
				assert(f_pskd_hpos == 0);
				assert(f_pskd_vpos == f_mix_vpos + 1);
			end else // if (f_mix_vpos == f_mix_height-1)
			begin
				assert(f_pskd_hpos == 0);
				assert(f_pskd_vpos == 0);
			end
		end
`endif
	end else begin : MATCH_ALPHA_PIPELINE
		assign	pskd_ready = !pix_line_pause
			&& (!pix_loaded || !mpy_loaded || !mix_valid
					|| !M_VID_TVALID || M_VID_TREADY);
		// {{{
		reg	pix_hlast, pix_vlast, pix_sof, r_pix_loaded;
		reg	r_mpy_loaded, mpy_hlast, mpy_vlast, mpy_sof;
		reg	mix_loaded, r_mix_hlast, r_mix_vlast, r_mix_sof;

		always @(posedge ACLK)
		if (!ARESETN)
			r_pix_loaded <= 0;
		else if (pskd_valid && pskd_ready)
			r_pix_loaded <= 1;
		else if (pix_ready)
			r_pix_loaded <= 0;

		always @(posedge ACLK)
		if (pskd_valid && pskd_ready)
		begin
			pix_hlast <= pskd_hlast;
			pix_vlast <= pskd_vlast;
			pix_sof   <= pskd_sof;
		end

		always @(posedge ACLK)
		if (!ARESETN)
			r_mpy_loaded <= 0;
		else if (pix_loaded && pix_ready)
			r_mpy_loaded<= 1;
		else if (mpy_ready)
			r_mpy_loaded <= 0;

		assign	mpy_loaded = r_mpy_loaded;

		always @(posedge ACLK)
		if (pix_loaded && pix_ready)
		begin
			mpy_hlast <= pix_hlast;
			mpy_vlast <= pix_vlast;
			mpy_sof   <= pix_sof;
		end

		always @(posedge ACLK)
		if (!ARESETN)
			mix_loaded <= 0;
		else if (mpy_loaded && mpy_ready)
			mix_loaded <= 1;
		else if (mix_ready)
			mix_loaded <= 0;

		always @(posedge ACLK)
		if (mpy_loaded && mpy_ready)
		begin
			r_mix_hlast <= mpy_hlast;
			r_mix_vlast <= mpy_vlast;
			r_mix_sof   <= mpy_sof;
		end


		assign	pix_loaded= r_pix_loaded;
		assign	mix_hlast = r_mix_hlast;
		assign	mix_vlast = r_mix_vlast;
		assign	mix_sof   = r_mix_sof;

		assign	mix_valid = mix_loaded;
		// }}}
	end endgenerate
	// }}}
	// }}}
	assign	ovskd_ready = frame_err
		|| !ov_line_pause && ((!in_overlay && !ovw_eof)
					|| (in_overlay && pskd_valid && pskd_ready));

	// M_VID_TVALID
	// {{{
	initial	M_VID_TVALID = 0;
	always @(posedge ACLK)
	if (!ARESETN)
		M_VID_TVALID <= 0;
	else if (!M_VID_TVALID || M_VID_TREADY)
		M_VID_TVALID <= mix_valid;
	// }}}

	// M_VID_TDATA, M_VID_TLAST, M_VID_TUSER
	// {{{
	always @(posedge ACLK)
	if (!M_VID_TVALID || M_VID_TREADY)
	begin
		M_VID_TDATA <= mix_pixel;
		if (OPT_TUSER_IS_SOF)
		begin
			M_VID_TLAST <= mix_hlast;
			M_VID_TUSER <= mix_sof;
		end else begin
			M_VID_TLAST <= mix_vlast;
			M_VID_TUSER <= mix_hlast;
		end
	end
	// }}}

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, lines_per_frame };
	// Verilator lint_on  UNUSED
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
	// Declarations
	// {{{
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!ARESETN);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Input properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge ACLK)
	begin
		assume($stable(i_enable));
		assume($stable(i_hpos));
		assume($stable(i_vpos));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Priority video slave input
	// {{{
	always @(posedge ACLK)
	if (!f_past_valid || $past(!ARESETN))
		assume(!S_PRI_TVALID);
	else if ($past(S_PRI_TVALID && !S_PRI_TREADY))
	begin
		assume(S_PRI_TVALID);
		assume($stable(S_PRI_TDATA));
		assume($stable(S_PRI_TLAST));
		assume($stable(S_PRI_TUSER));
	end
	// }}}

	// Overlay slave input
	// {{{
	always @(posedge ACLK)
	if (!f_past_valid || $past(!ARESETN))
		assume(!S_OVW_TVALID);
	else if ($past(S_OVW_TVALID && !S_OVW_TREADY))
	begin
		assume(S_OVW_TVALID);
		assume($stable(S_OVW_TDATA));
		assume($stable(S_OVW_TLAST));
		assume($stable(S_OVW_TUSER));
	end
	// }}}

	// Video output (master)
	// {{{
	always @(posedge ACLK)
	if (!f_past_valid || $past(!ARESETN))
		assume(!M_VID_TVALID);
	else if ($past(M_VID_TVALID && !M_VID_TREADY))
	begin
		assume(M_VID_TVALID);
		assume($stable(M_VID_TDATA));
		assume($stable(M_VID_TLAST));
		assume($stable(M_VID_TUSER));
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Video properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	begin
		assume(f_vid_width >= 4);
		assume(f_vid_height>= 4);

		assume(f_ovw_width >= 2);
		assume(f_ovw_height>= 2);
	end

	// f_pri_?pos
	// {{{
	initial f_pri_hpos = 0;
	initial f_pri_vpos = 0;
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		f_pri_hpos <= 0;
		f_pri_vpos <= 0;
	end else if (S_PRI_TVALID && S_PRI_TREADY)
	begin
		f_pri_hpos <= f_pri_hpos + 1;
		if (f_pri_hpos + 1 >= f_vid_width)
		begin
			f_pri_hpos <= 0;
			f_pri_vpos <= f_pri_vpos + 1;
			if (f_pri_vpos + 1 >= f_vid_height)
				f_pri_vpos <= 0;
		end
	end

	always @(*)
	begin
		assert(f_pri_hpos < f_vid_width);
		assert(f_pri_vpos < f_vid_height);
	end
	// }}}

	// f_ovw_?pos
	// {{{
	initial f_ovw_hpos = 0;
	initial f_ovw_vpos = 0;
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		f_ovw_hpos <= 0;
		f_ovw_vpos <= 0;
	end else if (S_OVW_TVALID && S_OVW_TREADY)
	begin
		f_ovw_hpos <= f_ovw_hpos + 1;
		if (f_ovw_hpos + 1 >= f_ovw_width)
		begin
			f_ovw_hpos <= 0;
			f_ovw_vpos <= f_ovw_vpos + 1;
			if (f_ovw_vpos + 1 >= f_ovw_height)
				f_ovw_vpos <= 0;
		end
	end

	always @(*)
	begin
		assert(f_ovw_hpos < f_ovw_width);
		assert(f_ovw_vpos < f_ovw_height);
	end
	// }}}

	// S_PRI_TLAST, S_PRI_TUSER
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin : ASSUME_SOF
		always @(*)
		if (S_PRI_TVALID)
		begin
			assume(S_PRI_TLAST == (f_pri_hpos == f_vid_width-1));
			assume(S_PRI_TUSER == (f_pri_hpos == 0 && f_pri_vpos == 0));
		end
	end else begin : ASSUME_VLAST
		always @(*)
		if (S_PRI_TVALID)
		begin
			assume(S_PRI_TUSER == (f_pri_hpos == f_vid_width-1));
			if (f_pri_vpos < f_vid_height-1)
				assume(!S_PRI_TLAST);
			else if (S_PRI_TUSER)
				assume(S_PRI_TLAST == (f_pri_vpos == f_vid_height-1));
		end
	end endgenerate
	// }}}

	// S_OVW_TLAST, S_OVW_TUSER
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin
		always @(*)
		if (S_OVW_TVALID)
		begin
			assume(S_OVW_TLAST == (f_ovw_hpos == f_ovw_width-1));
			assume(S_OVW_TUSER == (f_ovw_hpos == 0 && f_ovw_vpos == 0));
		end
	end else begin
		always @(*)
		if (S_OVW_TVALID)
		begin
			assume(S_OVW_TUSER == (f_ovw_hpos == f_ovw_width-1));
			if (f_ovw_vpos < f_ovw_height-1)
				assume(!S_OVW_TLAST);
			else if (S_OVW_TUSER)
				assume(S_OVW_TLAST == (f_ovw_vpos == f_ovw_height-1));
		end
	end endgenerate
	// }}}

	// f_vid_?pos
	// {{{
	initial f_vid_hpos = 0;
	initial f_vid_vpos = 0;
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		f_vid_hpos <= 0;
		f_vid_vpos <= 0;
	end else if (M_VID_TVALID && M_VID_TREADY)
	begin
		f_vid_hpos <= f_vid_hpos + 1;
		if (f_vid_hpos + 1 >= f_vid_width)
		begin
			f_vid_hpos <= 0;
			f_vid_vpos <= f_vid_vpos + 1;
			if (f_vid_vpos + 1 >= f_vid_height)
				f_vid_vpos <= 0;
		end
	end

	always @(*)
	begin
		assert(f_vid_hpos < f_vid_width);
		assert(f_vid_vpos < f_vid_height);
	end
	// }}}

	// M_VID_TLAST, M_VID_TUSER
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin : CHECK_OUTGOING_SOF
		always @(*)
		if (M_VID_TVALID)
		begin
			assert(M_VID_TLAST == (f_vid_hpos == f_vid_width-1));
			assert(M_VID_TUSER == (f_vid_hpos == 0 && f_vid_vpos == 0));
		end
	end else begin : CHECK_OUTGOING_VLAST
		always @(*)
		if (M_VID_TVALID)
		begin
			assert(M_VID_TUSER == (f_vid_hpos == f_vid_width-1));
			if (!M_VID_TUSER || f_vid_vpos < f_vid_height-1)
				assert(!M_VID_TLAST);
			else
				assert(M_VID_TLAST == (f_vid_vpos == f_vid_height-1));
		end
	end endgenerate
	// }}}

	// f_mix_?pos
	// {{{
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		f_mix_hpos <= 0;
		f_mix_vpos <= 0;
	end else if (mix_valid && mix_ready)
	begin
		f_mix_hpos <= f_mix_hpos + 1;
		if (f_mix_hpos == f_vid_width - 1)
		begin
			f_mix_hpos <= 0;
			f_mix_vpos <= f_mix_vpos + 1;
			if (f_mix_vpos == f_vid_height-1)
				f_mix_vpos <= 0;
		end
	end

	always @(*)
	if (ARESETN)
	begin
		assert(f_mix_hpos < f_vid_width);
		assert(f_mix_vpos < f_vid_height);
	end
	// }}}

	// f_mix_hlast, f_mix_sof, f_mix_vlast
	// {{{
	always @(*)
	if (ARESETN && mix_valid)
	begin
		assert(mix_hlast == (f_mix_hpos == f_vid_width-1));
		assert(mix_sof   == (f_mix_vpos == 0 && f_mix_hpos == 0));
		if (mix_vlast || f_pri_known)
			assert(mix_vlast == (mix_hlast && f_mix_vpos == f_vid_height-1));
	end
	// }}}

	always @(*)
	if (ARESETN)
	begin
		if (!M_VID_TVALID)
		begin
			assert(f_mix_hpos == f_vid_hpos);
			assert(f_mix_vpos == f_vid_vpos);
		end else if (f_vid_hpos < f_vid_width-1)
		begin
			assert(f_mix_hpos == f_vid_hpos + 1);
			assert(f_mix_vpos == f_vid_vpos);
		end else // if (f_vid_hpos == f_vid_width-1)
		begin
			assert(f_mix_hpos == 0);
			if (f_vid_vpos == f_vid_height-1)
				assert(f_mix_vpos == 0);
			else
				assert(f_mix_vpos == f_vid_vpos + 1);
		end
	end

	generate if (OPT_TUSER_IS_SOF)
	begin : CHECK_VLAST

		always @(*)
		if (ARESETN && lines_per_frame > 0)
		begin
			assert(lines_per_frame == f_vid_height);
			if (pskd_valid)
				assert(pskd_vlast == (pskd_hlast && f_pskd_vpos == f_vid_height-1));
		end else if (ARESETN)
		begin
			if (pskd_valid)
				assert(!pskd_vlast);
			if (mix_valid)
				assert(!mix_vlast);
		end

	end endgenerate

	// f_pskd_?pos
	// {{{
	initial f_pskd_hpos = 0;
	initial f_pskd_vpos = 0;
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		f_pskd_hpos <= 0;
		f_pskd_vpos <= 0;
	end else if (pskd_valid && pskd_ready)
	begin
		f_pskd_hpos <= f_pskd_hpos + 1;
		if (f_pskd_hpos + 1 >= f_vid_width)
		begin
			f_pskd_hpos <= 0;
			f_pskd_vpos <= f_pskd_vpos + 1;
			if (f_pskd_vpos + 1 >= f_vid_height)
				f_pskd_vpos <= 0;
		end
	end

	always @(*)
	if (ARESETN)
	begin
		assert(f_pskd_hpos < f_vid_width);
		assert(f_pskd_vpos < f_vid_height);
	end

	always @(*)
	if (ARESETN)
	begin
		if (1 || S_PRI_TREADY)
		begin
			assert(f_pskd_hpos == f_pri_hpos);
			assert(f_pskd_vpos == f_pri_vpos);
		end else if (f_vid_hpos > 0)
		begin
			assert(f_pskd_hpos + 1 == f_pri_hpos);
			assert(f_pskd_vpos <= f_pri_vpos);
		end else if (f_vid_vpos > 0)
		begin
			assert(f_pskd_hpos == f_vid_width -1);
			assert(f_pskd_vpos + 1 == f_pri_vpos);
		end else begin
			assert(f_pskd_hpos == f_vid_width -1);
			assert(f_pskd_vpos == f_vid_height - 1);
		end
	end
	// }}}

	// pskd_hlast, pskd_sof
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin : CHECK_LINES_PER_FRAME
		always @(posedge ACLK)
		if (f_past_valid && $past(ARESETN)
				&& $past(lines_per_frame == f_vid_height))
			assert(lines_per_frame == f_vid_height);
	end endgenerate

	always @(*)
	if (pskd_valid)
	begin
		assert(pskd_hlast == (f_pskd_hpos == f_vid_width-1));
		assert(pskd_sof   == (f_pskd_hpos == 0 && f_pskd_vpos == 0));
		if (lines_per_frame == f_vid_height)
			assert(pskd_vlast == (pskd_hlast && f_pskd_vpos == f_vid_height-1));
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Overlay tracking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge ACLK)
	if (ARESETN && (!OPT_LINE_BREAK || pskd_ready))
	begin
		if (f_pskd_hpos < i_hpos)
		begin
			assert(!in_overlay);
		end else if (f_pskd_vpos < i_vpos
				&& f_pskd_vpos == prvpos
				&& f_ovw_vpos == ovvpos
				&& f_pskd_hpos != 1)
			assert(!in_overlay);

		if (!frame_err && !ovw_eof && in_overlay
			&& lines_per_frame > 0)
		begin
			assert(i_hpos + f_ovw_hpos == f_pskd_hpos);
			if (f_ovw_vpos == ovvpos && f_pskd_vpos == prvpos
				&& f_pskd_hpos > 1
				&& ovhpos > 1)
				assert(i_vpos + f_ovw_vpos == f_pskd_vpos);
		end
	end
	// }}}
`endif
// }}}
endmodule
