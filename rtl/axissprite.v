////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axissprite.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Overlays a small sprite onto an AXI-stream video feed.  The
//		sprite is kept internally in block RAM, and can be updated from
//	the AXI-lite interface.  The position of the sprite on the screen can
//	also be controlled from register 0 of this interface.
//
// Registers:
//	0	Left-most pixel number, ranges from 0--screen width-1
//	2	Top-most pixel number, ranges from 0--screen height-1
//	(Half-end)	Sprite pixels.  Sprites are stored from top left,
//		to top right and on down.  The high order bit of the sprite
//		pixel, found in bit [24], indicates whether or not this sprite
//		pixel will replace its counterpart in the stream.  After that,
//		bits [23:16] are the red, [15:8] are green, and [7:0] are the
//		blue component of the sprite.
//
// Known issues:
//	Assumes no interlacing.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2021, Gisselquist Technology, LLC
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
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
// }}}
module	axissprite #(
		// {{{
		// XSIZE -- Width of the sprite in pixels
		parameter	XSIZE = 8,
		// YSIZE -- Height of the sprite in pixels
		parameter	YSIZE = 8,
		localparam	LGMEMSZ = $clog2(XSIZE*YSIZE),
		parameter	C_AXI_ADDR_WIDTH = 1+2+LGMEMSZ,
		// All AXI-lite interfaces have 32-bit data paths
		localparam	C_AXI_DATA_WIDTH = 32,
		// Use Skid buffers (required for AXI-stream compliance)
		parameter [0:0]	OPT_SKIDBUFFER = 1'b1,
		// OPT_LOWPOWER -- set unused registers to zero when !valid
		// (Not fully supported for this design ... yet, if ever)
		parameter [0:0]	OPT_LOWPOWER = 0,
		// OPT_TUSER_IS_SOF
		parameter [0:0] OPT_TUSER_IS_SOF = 0,
		//
		localparam	MEMSZ = (1<<LGMEMSZ),
		localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		//
		// AXI-lite interface
		// {{{
		// Write address channel
		input	wire					S_AXI_AWVALID,
		output	wire					S_AXI_AWREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]		S_AXI_AWADDR,
		input	wire	[2:0]				S_AXI_AWPROT,
		// Write data
		input	wire					S_AXI_WVALID,
		output	wire					S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_WDATA,
		input	wire	[C_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		// Write acknowledgment
		output	wire					S_AXI_BVALID,
		input	wire					S_AXI_BREADY,
		output	wire	[1:0]				S_AXI_BRESP,
		// Read address
		input	wire					S_AXI_ARVALID,
		output	wire					S_AXI_ARREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]		S_AXI_ARADDR,
		input	wire	[2:0]				S_AXI_ARPROT,
		// Read return data
		output	wire					S_AXI_RVALID,
		input	wire					S_AXI_RREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_RDATA,
		output	wire	[1:0]				S_AXI_RRESP,
		// }}}
		//
		// Incoming video
		// {{{
		input	wire		S_AXIS_TVALID,
		output	wire		S_AXIS_TREADY,
		input	wire	[23:0]	S_AXIS_TDATA,
		input	wire		S_AXIS_TLAST,	// HLAST && VLAST
		input	wire		S_AXIS_TUSER,	// HLAST
		// }}}
		//
		// Outgoing video
		// {{{
		output	reg		M_AXIS_TVALID,
		input	wire		M_AXIS_TREADY,
		output	reg	[23:0]	M_AXIS_TDATA,
		output	reg		M_AXIS_TLAST,	// HLAST && VLAST
		output	reg		M_AXIS_TUSER	// HLAST
		// }}}
		// }}}
	);

	////////////////////////////////////////////////////////////////////////
	//
	// Register/wire signal declarations
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire	i_reset = !S_AXI_ARESETN;

	wire					axil_write_ready;
	wire	[C_AXI_ADDR_WIDTH-ADDRLSB-1:0]	awskd_addr;
	//
	wire	[C_AXI_DATA_WIDTH-1:0]		wskd_data;
	wire [C_AXI_DATA_WIDTH/8-1:0]		wskd_strb;
	reg					axil_bvalid;
	//
	wire					axil_read_ready;
	wire	[C_AXI_ADDR_WIDTH-ADDRLSB-1:0]	arskd_addr;
	reg	[C_AXI_DATA_WIDTH-1:0]		axil_read_data;
	reg	[24:0]				axil_read_mem;
	reg					axil_read_valid,axil_pipe_valid,
						axil_read_reg;

	reg	[24:0]	spritemem	[0:MEMSZ-1];
	reg	[15:0]		r_top, r_left;
	reg	[15:0]		this_top, this_left;
	reg	[LGMEMSZ-1:0]	maddr;

	wire			vskd_valid, vskd_ready, vskd_hlast, vskd_vlast,
				vskd_sof;
	wire	[23:0]		vskd_data;
	reg			s_hlast, s_vlast, s_sof;
	reg	[15:0]		frame_x, frame_y;
	reg	[LGMEMSZ-1:0]	sprite_x, sprite_y;
	reg			in_sprite, in_sprite_x, in_sprite_y;
	reg	[24:0]		spritepix;

	reg			p_valid, p_hlast, p_vlast, p_sof;
	wire			p_step;
	reg	[23:0]		p_data;

	reg			S_AXIS_HLAST, S_AXIS_VLAST, S_AXIS_SOF;
	reg			M_AXIS_HLAST, M_AXIS_VLAST, M_AXIS_SOF;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite signaling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Write signaling
	//
	// {{{

	generate if (OPT_SKIDBUFFER)
	begin : SKIDBUFFER_WRITE
		// {{{
		wire	awskd_valid, wskd_valid;

		skidbuffer #(.OPT_OUTREG(0),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.DW(C_AXI_ADDR_WIDTH-ADDRLSB))
		axilawskid(//
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
			.i_data(S_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]),
			.o_valid(awskd_valid), .i_ready(axil_write_ready),
			.o_data(awskd_addr));

		skidbuffer #(.OPT_OUTREG(0),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.DW(C_AXI_DATA_WIDTH+C_AXI_DATA_WIDTH/8))
		axilwskid(//
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXI_WVALID), .o_ready(S_AXI_WREADY),
			.i_data({ S_AXI_WDATA, S_AXI_WSTRB }),
			.o_valid(wskd_valid), .i_ready(axil_write_ready),
			.o_data({ wskd_data, wskd_strb }));

		assign	axil_write_ready = awskd_valid && wskd_valid
				&& (!S_AXI_BVALID || S_AXI_BREADY);
		// }}}
	end else begin : SIMPLE_WRITES
		// {{{

		reg	axil_awready;

		initial	axil_awready = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			axil_awready <= 1'b0;
		else
			axil_awready <= !axil_awready
				&& (S_AXI_AWVALID && S_AXI_WVALID)
				&& (!S_AXI_BVALID || S_AXI_BREADY);

		assign	S_AXI_AWREADY = axil_awready;
		assign	S_AXI_WREADY  = axil_awready;

		assign 	awskd_addr = S_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB];
		assign	wskd_data  = S_AXI_WDATA;
		assign	wskd_strb  = S_AXI_WSTRB;

		assign	axil_write_ready = axil_awready;
		// }}}
	end endgenerate

	// axil_bvalid
	// {{{
	initial	axil_bvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_bvalid <= 0;
	else if (axil_write_ready)
		axil_bvalid <= 1;
	else if (S_AXI_BREADY)
		axil_bvalid <= 0;

	assign	S_AXI_BVALID = axil_bvalid;
	assign	S_AXI_BRESP = 2'b00;
	// }}}

	// }}}

	//
	// Read signaling
	//
	// {{{

	generate if (OPT_SKIDBUFFER)
	begin : SKIDBUFFER_READ
		// {{{
		wire	arskd_valid;

		skidbuffer #(.OPT_OUTREG(0),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.DW(C_AXI_ADDR_WIDTH-ADDRLSB))
		axilarskid(//
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
			.i_data(S_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]),
			.o_valid(arskd_valid), .i_ready(axil_read_ready),
			.o_data(arskd_addr));

		assign	axil_read_ready = arskd_valid
				&& (!axil_pipe_valid || !axil_read_valid || S_AXI_RREADY);
		// }}}
	end else begin : SIMPLE_READS
		// {{{
		reg	axil_arready;

		initial	axil_arready = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			axil_arready <= 1'b0;
		else
			axil_arready <= !axil_arready
				&& (S_AXI_ARVALID) && (!S_AXI_RVALID
					|| !axil_pipe_valid || S_AXI_RREADY);

		assign	arskd_addr = S_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB];
		assign	S_AXI_ARREADY = axil_arready;
		assign	axil_read_ready = (S_AXI_ARVALID && S_AXI_ARREADY && !axil_pipe_valid);
		// }}}
	end endgenerate

	// axil_pipe_valid
	// {{{
	initial	axil_pipe_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axil_pipe_valid <= 1'b0;
	else if (!axil_pipe_valid || !S_AXI_RVALID || S_AXI_RREADY)
		axil_pipe_valid <= axil_read_ready;
	// }}}

	// axil_read_valid
	// {{{
	initial	axil_read_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_read_valid <= 1'b0;
	else if (!S_AXI_RVALID || S_AXI_RREADY)
		axil_read_valid <= axil_pipe_valid;

	assign	S_AXI_RVALID = axil_read_valid;
	assign	S_AXI_RDATA  = axil_read_data;
	assign	S_AXI_RRESP = 2'b00;
	// }}}

	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite register logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Write to spritemem
	// {{{
	always @(posedge S_AXI_ACLK)
	if (axil_write_ready && awskd_addr[LGMEMSZ])
	begin
		if (wskd_strb[3])
			spritemem[awskd_addr[LGMEMSZ-1:0]][24] <= wskd_data[24];
		if (wskd_strb[2])
			spritemem[awskd_addr[LGMEMSZ-1:0]][23:16] <= wskd_data[23:16];
		if (wskd_strb[1])
			spritemem[awskd_addr[LGMEMSZ-1:0]][15:8] <= wskd_data[15:8];
		if (wskd_strb[0])
			spritemem[awskd_addr[LGMEMSZ-1:0]][7:0] <= wskd_data[7:0];
	end
	// }}}

	// Write to our sprite's position
	// {{{
	always @(posedge S_AXI_ACLK)
	if (axil_write_ready && !awskd_addr[LGMEMSZ-ADDRLSB])
		{ r_top, r_left } <= apply_wstrb({ r_top, r_left }, wskd_data,
					wskd_strb);
	// }}}

	// axil_read_mem: Read from memory
	// {{{
	initial	axil_read_mem = 0;
	always @(posedge S_AXI_ACLK)
	if (axil_read_ready)
		axil_read_mem <= spritemem[arskd_addr[LGMEMSZ-1:0]];
	// }}}

	// axil_read_reg : Are we reading from a memory or a register?
	// {{{
	initial	axil_read_reg = 0;
	always @(posedge S_AXI_ACLK)
	if (axil_read_ready)
		axil_read_reg <= arskd_addr[LGMEMSZ-ADDRLSB];
	// }}}

	// axil_read_data
	// {{{
	initial	r_left = 0;
	initial	r_top  = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_RVALID || S_AXI_RREADY)
	begin
		if (axil_read_reg)
			axil_read_data <= { r_top, r_left };
		else
			axil_read_data <= { 7'h0, axil_read_mem };

		if (OPT_LOWPOWER && !axil_pipe_valid)
			axil_read_data <= 0;
	end
	// }}}

	// apply_wstrb
	// {{{
	function [C_AXI_DATA_WIDTH-1:0]	apply_wstrb;
		input	[C_AXI_DATA_WIDTH-1:0]		prior_data;
		input	[C_AXI_DATA_WIDTH-1:0]		new_data;
		input	[C_AXI_DATA_WIDTH/8-1:0]	wstrb;

		integer	k;
		for(k=0; k<C_AXI_DATA_WIDTH/8; k=k+1)
		begin
			apply_wstrb[k*8 +: 8]
				= wstrb[k] ? new_data[k*8 +: 8] : prior_data[k*8 +: 8];
		end
	endfunction
	// }}}

	// End of AXI-lite register logic
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Video processing logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Adjust TLAST encoding (if necessary)
	generate if (OPT_TUSER_IS_SOF)
	begin : GENERATE_VLAST
		// {{{
		reg	[15:0]	line_count, lines_per_frame;
		reg		vlast;

		always @(*)
			S_AXIS_SOF = S_AXIS_TUSER;
		always @(*)
			S_AXIS_HLAST = S_AXIS_TLAST;

		initial	vlast  = 0;
		initial	lines_per_frame = 0;
		initial	line_count  = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			lines_per_frame <= 0;
			line_count      <= 0;
			vlast           <= 0;
		end else if (S_AXIS_TVALID && S_AXIS_TREADY)
		begin
			if (S_AXIS_SOF)
			begin
				line_count <= 0;
				lines_per_frame <= line_count;
			end else if (S_AXIS_HLAST)
				line_count <= line_count + 1;

			vlast <= (line_count + 1 == lines_per_frame);
			if (S_AXIS_SOF)
				vlast <= 1'b0;
		end

		always @(*)
			S_AXIS_HLAST = S_AXIS_TUSER;
		always @(*)
			S_AXIS_VLAST = S_AXIS_HLAST && vlast;
		// }}}
	end else begin : TLAST_IS_VLAST
		// {{{
		always @(*)
			S_AXIS_VLAST = S_AXIS_TLAST;
		always @(*)
			S_AXIS_HLAST = S_AXIS_TUSER;

		initial	S_AXIS_SOF = 1'b1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			S_AXIS_SOF <= 1'b1;
		else if (S_AXIS_TVALID && S_AXIS_TREADY)
			S_AXIS_SOF <= S_AXIS_VLAST;
		// }}}
	end endgenerate

	// The skidbuffer
	// {{{
	generate if (OPT_SKIDBUFFER)
	begin : SKIDBUFFER_VIDEO
		// {{{
		skidbuffer #(.OPT_OUTREG(0),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.DW(3+24))
		axisvskid(//
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
			.i_data({ S_AXIS_SOF, S_AXIS_VLAST, S_AXIS_HLAST, S_AXIS_TDATA }),
			.o_valid(vskd_valid), .i_ready(vskd_ready),
			.o_data({ vskd_sof, vskd_vlast, vskd_hlast, vskd_data }));

		// }}}
	end else begin : NO_SKID_VIDEO
		// {{{

		assign	S_AXIS_TREADY = vskd_ready;

		assign 	vskd_valid = S_AXIS_TVALID;
		assign	vskd_data  = S_AXIS_TDATA;
		assign	vskd_vlast = S_AXIS_VLAST;
		assign	vskd_hlast = S_AXIS_HLAST;
		assign	vskd_sof = S_AXIS_SOF;
		// }}}
	end endgenerate
	// }}}

	//
	// The first clock, coming out of the skid buffer
	//

	// s_hlast, s_vlast, s_sof
	// {{{
	always @(*)
		s_hlast = vskd_hlast;
	always @(*)
		s_vlast = vskd_vlast;
	always @(*)
		s_sof   = vskd_sof;
	// }}}

	// maddr, this_?pos, sprite_?, frame_?, in_sprite_?
	// {{{
	initial	maddr = 0;
	initial	this_top    = 0;
	initial	this_left   = 0;
	initial	frame_x     = 0;
	initial	frame_y     = 0;
	initial	sprite_x    = 0;
	initial	sprite_y    = 0;
	initial	in_sprite_x = 1;
	initial	in_sprite_y = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || (vskd_valid && vskd_ready && s_vlast))
	begin
		// Reset to top of frame
		// {{{
		maddr <= 0;

		this_top  <= r_top;
		this_left <= r_left;

		sprite_x <= 0;
		sprite_y <= 0;

		frame_x <= 0;
		frame_y <= 0;
		in_sprite_x <= (r_left == 0);
		in_sprite_y <= (r_top  == 0);
		// }}}
	end else if (vskd_valid && vskd_ready)
	begin

		// Memory address
		// {{{
		if (in_sprite_y && (s_hlast || (in_sprite_x && sprite_x < XSIZE-1)))
		begin
			if (s_hlast && (sprite_x < XSIZE))
				maddr <= maddr + XSIZE-sprite_x;
			else
				maddr <= maddr + 1;
		end
		// }}}

		// Frame pointer adjustment, in_sprite_?
		// {{{
		frame_x <= frame_x + 1;
		in_sprite_x <= (this_left <= frame_x + 1)
				&& (this_left + XSIZE > frame_x + 1);
		if (s_hlast)
		begin
			// New line
			frame_x <= 0;
			in_sprite_x <= (this_left == 0);
			frame_y <= frame_y + 1;

			in_sprite_y <= (this_top <= frame_y + 1)
				&& (this_top + YSIZE > frame_y + 1);
		end

		if (OPT_TUSER_IS_SOF && s_sof)
			frame_y <= 0;
		// }}}

		// Sprite position adjustment
		// {{{
		if (s_hlast)
			sprite_x <= 0;
		else if (in_sprite_x)
			sprite_x <= sprite_x + 1;
		if (in_sprite_y && s_hlast && sprite_y < YSIZE)
			sprite_y <= sprite_y + 1;
		// }}}
	end else if (OPT_TUSER_IS_SOF && vskd_valid && vskd_sof)
	begin
		maddr   <= 0;
		frame_y <= 0;
	end
	// }}}

	// maddr matches S_AXI* clock

	// spritepix--read from sprite memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (vskd_valid && vskd_ready)
		spritepix <= spritemem[maddr];
	// }}}

	// p_valid
	// {{{
	initial	p_valid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		p_valid <= 0;
	else if (vskd_valid && vskd_ready)
		p_valid <= 1;
	else if (p_step)
		p_valid <= 0;
	// }}}

	// p_hlast, p_vlast
	// {{{
	initial	{ p_sof, p_vlast, p_hlast } = { OPT_TUSER_IS_SOF, 2'b00 };
	always @(posedge S_AXI_ACLK)
	begin
		if (vskd_valid && vskd_ready)
			{ p_sof, p_vlast, p_hlast } <= { s_sof, s_vlast, s_hlast };

//		if (OPT_TUSER_IS_SOF)
//			p_vlast <= 1'b0;
//		else
//			p_sof <= 1'b0;
	end
	// }}}

	// p_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (vskd_valid && vskd_ready)
		p_data <= vskd_data;
	// }}}

	// in_sprite: is the 2nd stage from memory?
	// {{{
	always @(posedge S_AXI_ACLK)
	if (vskd_valid && vskd_ready)
		in_sprite <= (in_sprite_x && in_sprite_y);
	// }}}

	//
	// The 2nd clock
	//

	// M_AXIS_TVALID
	// {{{
	initial	M_AXIS_TVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIS_TVALID <= 1'b0;
	else if (!M_AXIS_TVALID || M_AXIS_TREADY)
		M_AXIS_TVALID <= p_valid;
	// }}}

	// M_AXIS_SOF, M_AXIS_HLAST, M_AXIS_VLAST
	// {{{
	initial	{ M_AXIS_SOF, M_AXIS_HLAST, M_AXIS_VLAST } = 3'b100;
	always @(posedge S_AXI_ACLK)
	if (!M_AXIS_TVALID || M_AXIS_TREADY)
		{ M_AXIS_SOF, M_AXIS_HLAST, M_AXIS_VLAST } <= { p_sof, p_hlast, p_vlast };
	// }}}

	// M_AXIS_TLAST, M_AXIS_TUSER
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin
		always @(*)
			{ M_AXIS_TLAST, M_AXIS_TUSER } = { M_AXIS_HLAST, M_AXIS_SOF};
		// Verilator lint_off UNUSED
		wire	unused_vlast;
		assign	unused_vlast = M_AXIS_VLAST;
		// Verilator lint_on UNUSED
	end else begin
		always @(*)
			{ M_AXIS_TLAST, M_AXIS_TUSER } = { M_AXIS_VLAST, M_AXIS_HLAST};

		// Verilator lint_off UNUSED
		wire	unused_sof;
		assign	unused_sof = M_AXIS_SOF;
		// Verilator lint_on UNUSED
	end endgenerate
	// }}}

	// M_AXIS_TDATA
	// {{{
	always @(posedge S_AXI_ACLK)
	if (p_step)
	begin
		if (in_sprite && spritepix[24])
			M_AXIS_TDATA <= spritepix[23:0];
		else
			M_AXIS_TDATA <= p_data;
	end
	// }}}

	//
	// Pipeline contol: vskd_ready && p_step
	// {{{
	assign	vskd_ready = p_step || !p_valid;
	assign	p_step = !M_AXIS_TVALID || M_AXIS_TREADY;
	// }}}

	// End of video logic
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXI_AWPROT, S_AXI_ARPROT,
			S_AXI_ARADDR[ADDRLSB-1:0],
			S_AXI_AWADDR[ADDRLSB-1:0] };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties used in verfiying this core
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-lite control interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_AXIL_LGDEPTH = 4;
	wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
					faxil_wr_outstanding,
					faxil_awr_outstanding;

	faxil_slave #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_LGDEPTH(F_AXIL_LGDEPTH),
		.F_AXI_MAXWAIT(2),
		.F_AXI_MAXDELAY(2),
		.F_AXI_MAXRSTALL(3),
		.F_OPT_COVER_BURST(4)
		// }}}
	) faxil(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		.i_axi_awaddr( S_AXI_AWADDR),
		.i_axi_awprot( S_AXI_AWPROT),
		//
		.i_axi_wvalid(S_AXI_WVALID),
		.i_axi_wready(S_AXI_WREADY),
		.i_axi_wdata( S_AXI_WDATA),
		.i_axi_wstrb( S_AXI_WSTRB),
		//
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		.i_axi_bresp( S_AXI_BRESP),
		//
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		.i_axi_araddr( S_AXI_ARADDR),
		.i_axi_arprot( S_AXI_ARPROT),
		//
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		.i_axi_rdata( S_AXI_RDATA),
		.i_axi_rresp( S_AXI_RRESP),
		//
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding)
		// }}}
		);

	// Bus invariants--relating outstanding counters to internals
	// {{{
	always @(*)
	if (OPT_SKIDBUFFER)
	begin
		assert(faxil_awr_outstanding== (S_AXI_BVALID ? 1:0)
			+(S_AXI_AWREADY ? 0:1));
		assert(faxil_wr_outstanding == (S_AXI_BVALID ? 1:0)
			+(S_AXI_WREADY ? 0:1));

		assert(faxil_rd_outstanding == (S_AXI_RVALID ? 1:0)
			+(axil_pipe_valid ? 1:0)
			+(S_AXI_ARREADY ? 0:1));
	end else begin
		assert(faxil_wr_outstanding == (S_AXI_BVALID ? 1:0));
		assert(faxil_awr_outstanding == faxil_wr_outstanding);

		assert(faxil_rd_outstanding == (S_AXI_RVALID ? 1:0)
			+(axil_pipe_valid ? 1:0));
	end
	// }}}

	// S_AXIS_RDATA && OPT_LOWPOWER
	// {{{
	// Check that our low-power only logic works by verifying that anytime
	// S_AXI_RVALID is inactive, then the outgoing data is also zero.
	//
	always @(*)
	if (OPT_LOWPOWER && !S_AXI_RVALID)
		assert(S_AXI_RDATA == 0);
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Video checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	f_vlast_locked, f_vskd_locked, fp_vlast_locked, fm_vlast_locked;
	reg	[15:0]	S_AXIS_XPOS, S_AXIS_YPOS, f_p_xpos, f_p_ypos,
			M_AXIS_XPOS, M_AXIS_YPOS, f_vskd_xpos, f_vskd_ypos;
	(* anyconst *) reg	[15:0]	f_lines_per_frame, f_pixels_per_line;


	//
	// AXI stream checks
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
		assume(!S_AXIS_TVALID);
	else if ($past(S_AXIS_TVALID&&!S_AXIS_TREADY))
		assume(S_AXIS_TVALID && $stable({ S_AXIS_TUSER, S_AXIS_TLAST,
				S_AXIS_TDATA }));

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
		assert(!p_valid);

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
		assert(!M_AXIS_TVALID);
	else if ($past(M_AXIS_TVALID&&!M_AXIS_TREADY))
		assert(M_AXIS_TVALID && $stable({ M_AXIS_TUSER, M_AXIS_TLAST,
				M_AXIS_TDATA }));
	// }}}

	// Count S_AXIS_XPOS and S_AXIS_YPOS
	// {{{
	initial	S_AXIS_XPOS = 0;
	initial	S_AXIS_YPOS = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		S_AXIS_XPOS <= 0;
		S_AXIS_YPOS <= 0;
	end else if (S_AXIS_TVALID && S_AXIS_TREADY)
	begin
		S_AXIS_XPOS <= S_AXIS_XPOS + 1;
		if (S_AXIS_XPOS + 1 >= f_pixels_per_line)
		begin
			S_AXIS_XPOS <= 0;
			S_AXIS_YPOS <= S_AXIS_YPOS + 1;
			if (S_AXIS_YPOS +1 >= f_lines_per_frame)
				S_AXIS_YPOS <= 0;
		end
	end

	always @(*)
	begin
		assert(S_AXIS_XPOS < f_pixels_per_line);
		assert(S_AXIS_YPOS < f_lines_per_frame);
		assume(!S_AXIS_TVALID
		|| S_AXIS_HLAST == (S_AXIS_XPOS == f_pixels_per_line-1));


		if (OPT_TUSER_IS_SOF)
			assume(!S_AXIS_TVALID || S_AXIS_SOF == (S_AXIS_XPOS == 0 && S_AXIS_YPOS == 0));
		else
			assume(!S_AXIS_TVALID || S_AXIS_VLAST == (S_AXIS_HLAST
				&& S_AXIS_YPOS == f_lines_per_frame-1));

		if (!OPT_TUSER_IS_SOF)
			assert(S_AXIS_SOF == (S_AXIS_XPOS == 0 && S_AXIS_YPOS == 0));
	end
	// }}}

	// Count f_vskd_xpos, and f_vskd_ypos
	// {{{
	generate if (OPT_SKIDBUFFER)
	begin
		// {{{
		initial	f_vskd_xpos = 0;
		initial	f_vskd_ypos = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			f_vskd_xpos <= 0;
			f_vskd_ypos <= 0;
		end else if (vskd_valid && vskd_ready)
		begin
			f_vskd_xpos <= f_vskd_xpos + 1;
			if (f_vskd_xpos +1 >= f_pixels_per_line)
			begin
				f_vskd_xpos <= 0;
				f_vskd_ypos  <= f_vskd_ypos + 1;
				if (f_vskd_ypos + 1 >= f_lines_per_frame)
					f_vskd_ypos <= 0;
			end
		end

		// Bounds checking on f_vskd*, vskd_hlast and vskd_sof checks
		// {{{
		always @(*)
		begin
			assert(f_vskd_xpos < f_pixels_per_line);
			assert(f_vskd_ypos < f_lines_per_frame);
			assert(!vskd_valid || vskd_hlast == (f_vskd_xpos == f_pixels_per_line-1));
			assert(!vskd_valid || vskd_sof == (f_vskd_xpos == 0 && f_vskd_ypos == 0));
			if (vskd_valid && f_vskd_locked)
				assert(vskd_vlast == (vskd_hlast
					&& f_vskd_ypos == f_lines_per_frame-1));
			else if (vskd_valid)
				assert(!vskd_vlast);
		end
		// }}}

		// Related f_vskd_* to S_AXIS_*
		// {{{
		always @(*)
		if (S_AXIS_TREADY)
		begin
			assert(f_vskd_xpos == S_AXIS_XPOS);
			assert(f_vskd_ypos == S_AXIS_YPOS);
		end else if (S_AXIS_XPOS > 0)
		begin
			assert(f_vskd_xpos + 1 == S_AXIS_XPOS);
			assert(f_vskd_ypos == S_AXIS_YPOS);
		end else if (S_AXIS_YPOS > 0)
		begin
			assert(f_vskd_xpos == f_pixels_per_line-1);
			assert(f_vskd_ypos + 1 == S_AXIS_YPOS);
		end else begin
			assert(f_vskd_xpos == f_pixels_per_line-1);
			assert(f_vskd_ypos == f_lines_per_frame-1);
		end
		// }}}
		// }}}
	end else begin
		always @(*)
			f_vskd_xpos = S_AXIS_XPOS;
		always @(*)
			f_vskd_ypos = S_AXIS_YPOS;
	end endgenerate
	// }}}

	// Count f_p_xpos, and f_p_ypos
	// {{{
	initial	f_p_xpos = 0;
	initial	f_p_ypos = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		f_p_xpos <= 0;
		f_p_ypos <= 0;
	end else if (p_valid && p_step)
	begin
		f_p_xpos <= f_vskd_xpos;
		f_p_ypos <= f_vskd_ypos;
	end

	always @(*)
	begin
		assert(f_p_xpos < f_pixels_per_line);
		assert(f_p_ypos < f_lines_per_frame);
		assert(!p_valid || p_hlast == (f_p_xpos == f_pixels_per_line-1));

		assert(!p_valid || p_sof == (f_p_xpos == 0 && f_p_ypos == 0));
		if (fp_vlast_locked && p_valid)
			assert(p_vlast == (p_hlast && f_p_ypos == f_lines_per_frame-1));
		else if (p_valid)
			assert(!p_vlast);
	end

	always @(*)
	if (!p_valid) // && !vskd_valid)
	begin
		assert(f_p_xpos == f_vskd_xpos);
		assert(f_p_ypos == f_vskd_ypos);
	end else if (f_vskd_xpos > 0)
	begin
		assert(f_p_xpos + 1 == f_vskd_xpos);
		assert(f_p_ypos == f_vskd_ypos);
	end else if (f_vskd_ypos > 0)
	begin
		assert(f_p_xpos == f_pixels_per_line-1);
		assert(f_p_ypos + 1 == f_vskd_ypos);
	end else begin
		assert(f_p_xpos == f_pixels_per_line-1);
		assert(f_p_ypos == f_lines_per_frame-1);
	end
	// }}}

	// Count M_AXIS_XPOS and M_AXIS_YPOS
	// {{{
	initial	M_AXIS_XPOS = 0;
	initial	M_AXIS_YPOS = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		M_AXIS_XPOS <= 0;
		M_AXIS_YPOS <= 0;
	end else if (M_AXIS_TVALID && M_AXIS_TREADY)
	begin
		M_AXIS_XPOS <= M_AXIS_XPOS + 1;
		if (M_AXIS_XPOS + 1 >= f_pixels_per_line)
		begin
			M_AXIS_XPOS <= 0;
			M_AXIS_YPOS <= M_AXIS_YPOS + 1;
			if (M_AXIS_YPOS +1 >= f_lines_per_frame)
				M_AXIS_YPOS <= 0;
		end
	end

	// Limits, and M_AXIS_HLAST, M_AXIS_SOF
	// {{{
	always @(*)
	begin
		assert(M_AXIS_XPOS < f_pixels_per_line);
		assert(M_AXIS_YPOS < f_lines_per_frame);
		assert(!M_AXIS_TVALID
			|| M_AXIS_HLAST == (M_AXIS_XPOS == f_pixels_per_line-1));
		if (M_AXIS_TVALID)
		begin
			assert(M_AXIS_SOF == (M_AXIS_XPOS == 0 && M_AXIS_YPOS == 0));
			if (fm_vlast_locked)
				assert(M_AXIS_VLAST == (M_AXIS_HLAST && M_AXIS_YPOS == f_lines_per_frame-1));
			else
				assert(!M_AXIS_VLAST);
		end
	end
	// }}}

	// Relate f_p_* to M_AXIS_*
	// {{{
	always @(*)
	if (!M_AXIS_TVALID)
	begin
		assert(f_p_xpos == M_AXIS_XPOS);
		assert(f_p_ypos == M_AXIS_YPOS);
	end else if (f_p_xpos != 0)
	begin
		assert(f_p_xpos == M_AXIS_XPOS + 1);
		assert(f_p_ypos == M_AXIS_YPOS);
	end else if (f_p_ypos > 0)
	begin
		assert(M_AXIS_XPOS == f_pixels_per_line-1);
		assert(f_p_ypos == M_AXIS_YPOS + 1);
	end else begin
		assert(M_AXIS_XPOS == f_pixels_per_line-1);
		assert(M_AXIS_YPOS == f_lines_per_frame-1);
	end
	// }}}

	// }}}

	// frame_x and frame_y
	// {{{
	always @(*)
	begin
		if (OPT_TUSER_IS_SOF)
			assert(frame_y <= f_lines_per_frame);
		else
			assert(frame_y < f_lines_per_frame);

		assert(frame_x < f_pixels_per_line);
		assert(frame_x == f_vskd_xpos);
		if (!OPT_TUSER_IS_SOF || f_vskd_locked)
			assert(frame_y == f_vskd_ypos);
		else if (frame_x != 0)
			assert(frame_y == f_vskd_ypos);
		else if (frame_y != 0)
		begin
			if (frame_y != f_vskd_ypos)
			begin
				assert(f_vskd_ypos == 0);
				assert(frame_y == f_lines_per_frame);
				assert(frame_x == 0);
			end
		end else
			assert(f_vskd_ypos == 0 && f_vskd_xpos == 0);
	end
	// }}}

	generate if (OPT_TUSER_IS_SOF)
	begin : CHECK_VLAST
		// {{{
		always @(*)
			assert(GENERATE_VLAST.line_count <= f_lines_per_frame);

		always @(*)
		if (GENERATE_VLAST.lines_per_frame != 0)
			assert(GENERATE_VLAST.lines_per_frame == f_lines_per_frame);

		// always @(*)
		// if (GENERATE_VLAST.line_count != f_lines_per_frame)
			// assume(!S_AXIS_SOF);

		always @(*)
			f_vlast_locked = (GENERATE_VLAST.lines_per_frame != 0);

		if (OPT_SKIDBUFFER)
		begin
			initial	f_vskd_locked = 1'b0;
			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				f_vskd_locked <= 1'b0;
			else if (!vskd_valid || vskd_ready)
				f_vskd_locked <= f_vlast_locked;
		end else begin
			always @(*)
				f_vskd_locked = f_vlast_locked;
		end

		initial	fp_vlast_locked = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			fp_vlast_locked <= 1'b0;
		else if (vskd_valid && vskd_ready)
			fp_vlast_locked <= f_vskd_locked;

		initial	fm_vlast_locked = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			fm_vlast_locked <= 1'b0;
		else if (!M_AXIS_TVALID || M_AXIS_TREADY)
			fm_vlast_locked <= fp_vlast_locked;

		always @(*)
		case({ f_vlast_locked, f_vskd_locked, fp_vlast_locked, fm_vlast_locked})
		4'b0000: begin end
		4'b1000: begin assert(S_AXIS_XPOS == 1 && S_AXIS_YPOS == 0); end
		4'b1100: begin assert(f_vskd_xpos == 1 && f_vskd_ypos == 0 && p_sof); end
		4'b1110: begin end
		4'b1111: begin end
		default: assert(0);
		endcase

		always @(*)
			assert(frame_y <= f_lines_per_frame);
		always @(*)
		if (f_vlast_locked)
			assert(frame_y < f_lines_per_frame);
		// }}}
	end else begin : ASSUME_VLAST_VALID
		// {{{
		always @(*)
		begin
			f_vlast_locked  = 1'b1;
			f_vskd_locked   = 1'b1;
			fp_vlast_locked = 1'b1;
			fm_vlast_locked = 1'b1;
		end
		// }}}
	end endgenerate

	always @(*)
	begin
		assert(sprite_x <= XSIZE);
		assert(sprite_y <= YSIZE);

		if (frame_y < this_top)
			assert(!f_vlast_locked || maddr == 0);
		else if (f_vskd_locked && in_sprite_y && XSIZE == (1<<$clog2(XSIZE)))
		begin
			if (frame_x >= this_left + XSIZE)
				assert(maddr == (sprite_y << $clog2(XSIZE)) + XSIZE-1);
			else
				assert(maddr == (sprite_y << $clog2(XSIZE)) + sprite_x);
		end

		assert(in_sprite_x == ((frame_x >= this_left)
					&& (frame_x < this_left + XSIZE)));
		assert(in_sprite_y == ((frame_y >= this_top)
					&& (frame_y < this_top + YSIZE)));

		if (in_sprite_x)
			assert(sprite_x == (frame_x - this_left));
		else if (frame_x < this_left)
			assert(sprite_x == 0);
		else
			assert(sprite_x == XSIZE);
		if (in_sprite_y)
			assert(sprite_y == (frame_y - this_top));
		else if (!OPT_TUSER_IS_SOF || frame_x > 1 || f_vskd_locked
				|| frame_y < f_lines_per_frame)
			assert((sprite_y != 0) ==(frame_y >= this_top + YSIZE));
	end

	always @(*)
	if (p_valid && p_vlast)
	begin
		assert(maddr == 0);
		assert(sprite_x == 0);
		assert(sprite_y == 0);
		assert(frame_x == 0);
		assert(frame_y == 0);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[3:0]	cvr_frames, cvr_pframes, cvr_skdframes;

	initial	cvr_skdframes = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_skdframes <= 0;
	else if (M_AXIS_TVALID && M_AXIS_TREADY)
	begin
		if (OPT_TUSER_IS_SOF && vskd_sof)
			cvr_skdframes <= cvr_skdframes + 1;
		else if (!OPT_TUSER_IS_SOF && vskd_vlast)
			cvr_skdframes <= cvr_skdframes + 1;
	end

	always @(*)
	begin
		cover(cvr_skdframes == 1);
		cover(cvr_skdframes == 2);
		cover(cvr_skdframes > 2);
	end

	initial	cvr_pframes = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_pframes <= 0;
	else if (M_AXIS_TVALID && M_AXIS_TREADY)
	begin
		if (OPT_TUSER_IS_SOF && p_sof)
			cvr_pframes <= cvr_pframes + 1;
		else if (!OPT_TUSER_IS_SOF && p_vlast)
			cvr_pframes <= cvr_pframes + 1;
	end

	always @(*)
	begin
		cover(cvr_pframes == 1);
		cover(cvr_pframes == 2);
		cover(cvr_pframes > 2);
	end

	initial	cvr_frames = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_frames <= 0;
	else if (M_AXIS_TVALID && M_AXIS_TREADY)
	begin
		if (OPT_TUSER_IS_SOF && M_AXIS_TUSER)
			cvr_frames <= cvr_frames + 1;
		else if (!OPT_TUSER_IS_SOF && M_AXIS_TLAST)
			cvr_frames <= cvr_frames + 1;
	end

	always @(*)
	begin
		cover(cvr_frames == 1);
		cover(cvr_frames == 2);
		cover(cvr_frames > 2);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
		assume(f_pixels_per_line > 1);
	always @(*)
		assume(f_lines_per_frame > 1);

	cover property (@(posedge S_AXI_ACLK)
		S_AXI_ARESETN && S_AXIS_TREADY && S_AXIS_TVALID throughout (
			!S_AXIS_HLAST
			##1 S_AXIS_HLAST
			##1 !S_AXIS_HLAST
			##1 S_AXIS_HLAST && S_AXIS_VLAST)
		);
	// }}}
`endif
// }}}
endmodule

