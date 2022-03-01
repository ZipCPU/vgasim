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
//		to top right and on down.  The high order bits of the sprite
//		pixel, found in bits [24 +: ALPHA_BITS], indicates whether or
//		not this sprite pixel will replace its counterpart in the
//		stream and to what extend.  After that, bits [23:16] are the
//		red, [15:8] are green, and [7:0] are the blue component of the
//		sprite.  (This ordering is arbitrary.  If you swap pixel
//		orders, just swap the order in memory and all will continue
//		as desired.)
//
// Known issues:
//	Assumes no interlacing.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2022, Gisselquist Technology, LLC
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
		// LGFRAME: number of bits required by a position counter
		parameter	LGFRAME = 16,
		// XSIZE -- Width of the sprite in pixels
		parameter	XSIZE = 8,
		// YSIZE -- Height of the sprite in pixels
		parameter	YSIZE = 8,
		parameter	BITS_PER_COLOR = 8,
		localparam	BPC = BITS_PER_COLOR,
		localparam	BPP = 3 * BITS_PER_COLOR,
		localparam	SBPC = (BPC > 8) ? 8 : BPC,
		parameter	ALPHA_BITS = 1,
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
		parameter	INITIAL_MEM = "",
		//
		localparam	MEMSZ = (1<<LGMEMSZ),
		localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		//
		input	wire	S_VID_ACLK,
		input	wire	S_VID_ARESETN,
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
		input	wire	[BPP-1:0]	S_AXIS_TDATA,
		input	wire		S_AXIS_TLAST,	// HLAST && VLAST
		input	wire		S_AXIS_TUSER,	// HLAST
		// }}}
		//
		// Outgoing video
		// {{{
		output	reg		M_AXIS_TVALID,
		input	wire		M_AXIS_TREADY,
		output	reg	[BPP-1:0]	M_AXIS_TDATA,
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
	reg	[3*SBPC+ALPHA_BITS-1:0]		axil_read_mem;
	reg					axil_read_valid,axil_pipe_valid,
						axil_read_reg;

	reg	[3*SBPC+ALPHA_BITS-1:0]	spritemem	[0:MEMSZ-1];
	reg	[LGFRAME-1:0]		bus_top, bus_left,
					staged_top, staged_left,
					this_top, this_left,
					last_line_no;
	reg	[LGMEMSZ-1:0]		maddr;

	wire			vskd_valid, vskd_ready, vskd_hlast, vskd_vlast,
				vskd_sof;
	wire	[BPP-1:0]		vskd_data;
	wire			s_hlast, s_vlast, s_sof;
	reg	[LGFRAME-1:0]		frame_x, frame_y;
	reg	[LGMEMSZ-1:0]	sprite_x, sprite_y;
	reg			in_sprite, in_sprite_x, in_sprite_y;
	reg	[3*SBPC + ALPHA_BITS-1:0]		spritepix;

	reg			p_valid, p_hlast, p_vlast, p_sof;
	wire			p_step;
	reg	[BPP-1:0]		p_data;

	wire			S_AXIS_HLAST, S_AXIS_VLAST, S_AXIS_SOF;

	reg				bus_last_line, pipe_last_line,
					last_line;
	reg	[C_AXI_DATA_WIDTH-1:0]	last_bus_pos;

	wire	[7:0]	alpha_byte;
	reg	[31:0]	bus_memword;
`ifdef	FORMAL
	// {{{
	(* gclk *)	reg	gbl_clk;
	reg	f_past_valid, f_past_valid_vid, f_past_valid_bus;
	wire			f_vlast_locked, f_vskd_locked, fp_vlast_locked;
	reg			fm_vlast_locked;
	wire	[LGFRAME-1:0]	f_vskd_xpos, f_vskd_ypos;
	wire	[LGFRAME-1:0]	S_AXIS_XPOS, S_AXIS_YPOS;
	wire			fs_vlast, fs_hlast, fs_sof, fs_known;

	wire			fM_vlast, fM_hlast, fM_sof, fM_known;
	wire	[LGFRAME-1:0]	fp_xpos, fp_ypos;
	wire	[LGFRAME-1:0]	M_AXIS_XPOS, M_AXIS_YPOS;
	(* anyconst *) reg	[LGFRAME-1:0]	f_lines_per_frame,
						f_pixels_per_line;
	// }}}
`endif

	// Verilator lint_off WIDTH
	generate if (INITIAL_MEM != "")
	begin : GEN_READMEMH
	// Verilator lint_on  WIDTH
		initial $readmemh(INITIAL_MEM, spritemem);
	end endgenerate

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
	generate if (ALPHA_BITS > 0)
	begin : GEN_SET_ALPHAMEM
		always @(posedge S_AXI_ACLK)
		if (axil_write_ready && awskd_addr[LGMEMSZ] && wskd_strb[3])
			spritemem[awskd_addr[LGMEMSZ-1:0]][3*SBPC +: ALPHA_BITS] <= wskd_data[24 +: ALPHA_BITS];
	end endgenerate

	always @(posedge S_AXI_ACLK)
	if (axil_write_ready && awskd_addr[LGMEMSZ])
	begin
		if (wskd_strb[2])
			spritemem[awskd_addr[LGMEMSZ-1:0]][2*SBPC +: SBPC]
					<= wskd_data[23:24-SBPC];
		if (wskd_strb[1])
			spritemem[awskd_addr[LGMEMSZ-1:0]][SBPC +: SBPC]
					<= wskd_data[15:16-SBPC];
		if (wskd_strb[0])
			spritemem[awskd_addr[LGMEMSZ-1:0]][SBPC-1:0]
					<= wskd_data[7:8-SBPC];
	end
	// }}}

	// Write to our sprite's position
	// {{{
	always @(*)
	begin
		last_bus_pos = 0;

		last_bus_pos[16 +: LGFRAME] = bus_top;
		last_bus_pos[0  +: LGFRAME] = bus_left;
	end

	always @(posedge S_AXI_ACLK)
	if (axil_write_ready && !awskd_addr[LGMEMSZ-ADDRLSB])
		{ bus_top, bus_left } <= apply_wstrb(last_bus_pos, wskd_data,
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

	// alpha_byte
	// {{{
	generate if (ALPHA_BITS > 0)
	begin : GEN_RETURN_ALPHA
		// {{{
		reg	[7:0]	r_alpha_byte;
		always @(*)
		begin
			r_alpha_byte = 0;
			r_alpha_byte[ALPHA_BITS-1:0]
					= axil_read_mem[3*BPC +: ALPHA_BITS];
		end

		assign	alpha_byte = r_alpha_byte;
		// }}}
	end else begin
		assign	alpha_byte = 0;
	end endgenerate
	// }}}

	// bus_memword
	// {{{
	always @(*)
	begin
		bus_memword = 0;
		bus_memword[31:24] = alpha_byte;
		bus_memword[23:24-SBPC] = axil_read_mem[2*SBPC +: SBPC];
		bus_memword[15:16-SBPC] = axil_read_mem[1*SBPC +: SBPC];
		bus_memword[ 7: 8-SBPC] = axil_read_mem[0*SBPC +: SBPC];
	end
	// }}}

	// axil_read_data
	// {{{
	initial	bus_left = 0;
	initial	bus_top  = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_RVALID || S_AXI_RREADY)
	begin
		if (axil_read_reg)
			axil_read_data <= { bus_top, bus_left };
		else begin
			axil_read_data <= bus_memword;
		end

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
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin : GENERATE_VLAST
		// {{{
		reg	[LGFRAME-1:0]	line_count, lines_per_frame;
		reg		vlast;

		initial	vlast  = 0;
		initial	lines_per_frame = 0;
		initial	line_count  = 0;
		always @(posedge S_VID_ACLK)
		if (!S_VID_ARESETN)
		begin
			lines_per_frame <= 0;
			line_count      <= 0;
			vlast           <= 0;
		end else if (S_AXIS_TVALID && S_AXIS_TREADY)
		begin
			vlast <= (line_count + 1 == lines_per_frame);

			if (S_AXIS_SOF)
			begin
				line_count <= 0;
				lines_per_frame <= line_count;
			end else if (S_AXIS_HLAST)
			begin
				line_count <= line_count + 1;
				vlast <= (line_count + 2 == lines_per_frame);
			end
			if (S_AXIS_SOF)
				vlast <= 1'b0;
		end

		assign	S_AXIS_SOF = S_AXIS_TUSER;
		assign	S_AXIS_HLAST = S_AXIS_TLAST;
		assign	S_AXIS_VLAST = S_AXIS_HLAST && vlast;
`ifdef	FORMAL
		// {{{
		assign	f_vlast_locked = (lines_per_frame != 0);
		always @(*)
			assert(line_count <= f_lines_per_frame);

		always @(*)
		if (fs_sof && fs_known)
		begin
			assert(line_count == f_lines_per_frame);
		end else
			assert(line_count == S_AXIS_YPOS);

		always @(*)
		if (lines_per_frame != 0)
			assert(lines_per_frame == f_lines_per_frame);
		always @(*)
		if (lines_per_frame == 0 && fs_known)
		begin
			assert(line_count == f_lines_per_frame);
			assert(S_AXIS_YPOS == 0 && S_AXIS_XPOS == 0);
		end else if (!fs_known)
			assert(lines_per_frame == 0);
		always @(*)
		if (f_vlast_locked)
			assert(vlast == (S_AXIS_YPOS == lines_per_frame-1));
		else
			assert(!vlast);
		// }}}
`endif
		// }}}
	end else begin : TLAST_IS_VLAST
		// {{{
		reg	sof;

		assign	S_AXIS_VLAST = S_AXIS_TLAST;
		assign	S_AXIS_HLAST = S_AXIS_TUSER;

		initial	sof = 1'b1;
		always @(posedge S_VID_ACLK)
		if (!S_VID_ARESETN)
			sof <= 1'b1;
		else if (S_AXIS_TVALID && S_AXIS_TREADY)
			sof <= S_AXIS_VLAST;

		assign	S_AXIS_SOF = sof;
`ifdef	FORMAL
		assign	f_vlast_locked = 1;
`endif
		// }}}
	end endgenerate
	// }}}

	// The skidbuffer
	// {{{
	generate if (OPT_SKIDBUFFER)
	begin : SKIDBUFFER_VIDEO
		// {{{
		skidbuffer #(
			// {{{
			.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(3+24)
			// }}}
		) axisvskid(
			// {{{
			.i_clk(S_VID_ACLK), .i_reset(!S_VID_ARESETN),
			.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
			.i_data({ S_AXIS_SOF, S_AXIS_VLAST, S_AXIS_HLAST, S_AXIS_TDATA }),
			.o_valid(vskd_valid), .i_ready(vskd_ready),
			.o_data({ vskd_sof, vskd_vlast, vskd_hlast, vskd_data })
			// }}}
		);

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
	assign	s_hlast = vskd_hlast;
	assign	s_vlast = vskd_vlast;
	assign	s_sof   = vskd_sof;
	// }}}

	always @(posedge S_AXI_ACLK)
		{ bus_last_line, pipe_last_line } <= { pipe_last_line, last_line };
	always @(posedge S_AXI_ACLK)
	if (!bus_last_line)
	begin
		staged_top  <= bus_top;
		staged_left <= bus_left;
	end

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
	always @(posedge S_VID_ACLK)
	if (!S_VID_ARESETN || (vskd_valid && vskd_ready && s_vlast))
	begin
		// Reset to top of frame
		// {{{
		maddr <= 0;

		this_top  <= staged_top;
		this_left <= staged_left;

		sprite_x <= 0;
		sprite_y <= 0;

		frame_x <= 0;
		frame_y <= 0;
		in_sprite_x <= (staged_left == 0);
		in_sprite_y <= (staged_top  == 0);

		last_line_no <= frame_y;
		last_line <= 0;
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

		last_line <= (frame_y == last_line_no);
	end else if (OPT_TUSER_IS_SOF && vskd_valid && vskd_sof)
	begin
		maddr   <= 0;
		frame_y <= 0;

		last_line <= 0;
	end
	// }}}

	// maddr matches S_AXI* clock

	// spritepix--read from sprite memory
	// {{{
	always @(posedge S_VID_ACLK)
	if (vskd_valid && vskd_ready)
		spritepix <= spritemem[maddr];
	// }}}

	// p_valid
	// {{{
	initial	p_valid = 0;
	always @(posedge S_VID_ACLK)
	if (!S_VID_ARESETN)
		p_valid <= 0;
	else if (vskd_valid && vskd_ready)
		p_valid <= 1;
	else if (p_step)
		p_valid <= 0;
	// }}}

	// p_hlast, p_vlast
	// {{{
	initial	{ p_sof, p_vlast, p_hlast } = { OPT_TUSER_IS_SOF, 2'b00 };
	always @(posedge S_VID_ACLK)
	if (!S_VID_ARESETN)
	begin
		{ p_sof, p_vlast, p_hlast } <= { OPT_TUSER_IS_SOF, 2'b00 };
	end else begin
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
	always @(posedge S_VID_ACLK)
	if (vskd_valid && vskd_ready)
		p_data <= vskd_data;
	// }}}

	// in_sprite: is the 2nd stage from memory?
	// {{{
	always @(posedge S_VID_ACLK)
	if (vskd_valid && vskd_ready)
		in_sprite <= (in_sprite_x && in_sprite_y);
	// }}}

	//
	// The 2nd (and subsequent) clock(s)
	//

	generate if (ALPHA_BITS > 1)
	begin : GEN_ALPHA_CLOCKS
		// {{{
		reg	[SBPC+ALPHA_BITS-1:0]	rsp,  gsp,  bsp;
		reg	[BPC + ALPHA_BITS-1:0]	rdat, gdat, bdat;
		reg	[BPC + ALPHA_BITS:0]	rpx,  gpx,  bpx;
		reg	[BPC-1:0]		rcpy, gcpy, bcpy;
		wire		a1_step,  a2_step, a3_step;
		reg		a1_valid, a1_tlast, a1_tuser, a1_insprite;
		reg		a2_valid, a2_tlast, a2_tuser;
		wire	[ALPHA_BITS-1:0]	alpha, alphan;

		// alpha_data
		wire	[SBPC-1:0]	sr, sg, sb;
		wire	[BPC-1:0]	pr, pg, pb;

		assign	alpha  =  spritepix[3*SBPC +: ALPHA_BITS];
		assign	alphan = ~spritepix[3*SBPC +: ALPHA_BITS];
		assign	sr = spritepix[2*SBPC +: SBPC];
		assign	sg = spritepix[1*SBPC +: SBPC];
		assign	sb = spritepix[0*SBPC +: SBPC];
		assign	pr = p_data[2*BPC +: BPC];
		assign	pg = p_data[1*BPC +: BPC];
		assign	pb = p_data[0*BPC +: BPC];
`ifdef	FORMAL
		(* anyseq *) reg	[SBPC+ALPHA_BITS-1:0]	f_rsp,  f_gsp,  f_bsp;
		(* anyseq *) reg	[BPC + ALPHA_BITS-1:0]	f_rdat, f_gdat, f_bdat;
`else
		always @(posedge S_VID_ACLK)
		if (a1_step)
		begin
			rsp <= sr * alpha;
			gsp <= sg * alpha;
			bsp <= sb * alpha;

			rdat <= pr * alphan;
			gdat <= pg * alphan;
			bdat <= pb * alphan;
		end
`endif

		always @(posedge S_VID_ACLK)
		if (a1_step)
		begin
			{ rcpy, gcpy, bcpy } <= p_data;

			a1_insprite <= in_sprite;
		end

		always @(posedge S_VID_ACLK)
		if (a2_step)
		begin
			if (a1_insprite)
			begin
				rpx <= rsp + rdat;
				gpx <= gsp + gdat;
				bpx <= bsp + bdat;
			end else begin
				{ rpx, gpx, bpx } <= 0;
				rpx[ALPHA_BITS +: BPC] <= rcpy;
				gpx[ALPHA_BITS +: BPC] <= gcpy;
				bpx[ALPHA_BITS +: BPC] <= bcpy;
			end
		end

		always @(posedge S_VID_ACLK)
		if (a3_step)
		begin
			M_AXIS_TDATA[2*BPC +: BPC] <= rpx[ALPHA_BITS +: BPC];
			M_AXIS_TDATA[1*BPC +: BPC] <= gpx[ALPHA_BITS +: BPC];
			M_AXIS_TDATA[0*BPC +: BPC] <= bpx[ALPHA_BITS +: BPC];

			if (rpx[BPC+ALPHA_BITS]) M_AXIS_TDATA[2*BPC +: BPC] <= -1;
			if (gpx[BPC+ALPHA_BITS]) M_AXIS_TDATA[1*BPC +: BPC] <= -1;
			if (bpx[BPC+ALPHA_BITS]) M_AXIS_TDATA[0*BPC +: BPC] <= -1;
		end

		// a1_valid
		// {{{
		initial	a1_valid = 1'b0;
		always @(posedge S_VID_ACLK)
		if (!S_VID_ARESETN)
			a1_valid <= 1'b0;
		else if (a1_step)
			a1_valid <= p_valid;
		// }}}

		// a1_tlast, a1_tuser
		// {{{
		always @(posedge S_VID_ACLK)
		if (a1_step)
		begin
			if (OPT_TUSER_IS_SOF)
			begin
				{ a1_tlast, a1_tuser } <= { p_hlast, p_sof};
			end else begin
				{ a1_tlast, a1_tuser } <= { p_vlast, p_hlast };
			end
		end
		// }}}

		// a2_valid, a2_tlast, a2_tuser
		// {{{
		initial	a2_valid = 1'b0;
		always @(posedge S_VID_ACLK)
		if (!S_VID_ARESETN)
			a2_valid <= 1'b0;
		else if (a2_step)
			a2_valid <= a1_valid;

		always @(posedge S_VID_ACLK)
		if (a2_step)
			{ a2_tlast, a2_tuser } <= { a1_tlast, a1_tuser };
		// }}}

		// M_AXIS_TVALID, M_AXIS_TLAST, M_AXIS_TUSER
		// {{{
		initial	M_AXIS_TVALID = 1'b0;
		always @(posedge S_VID_ACLK)
		if (!S_VID_ARESETN)
			M_AXIS_TVALID <= 1'b0;
		else if (a3_step)
			M_AXIS_TVALID <= a2_valid;

		always @(posedge S_VID_ACLK)
		if (a3_step)
			{ M_AXIS_TLAST, M_AXIS_TUSER } <= { a2_tlast, a2_tuser };
		// }}}

		assign	vskd_ready = p_step  || !p_valid;
		assign	p_step     = a1_step || !p_valid;
		assign	a1_step    = a2_step || !a1_valid;
		assign	a2_step    = a3_step || !a2_valid;
		assign	a3_step    = !M_AXIS_TVALID || M_AXIS_TREADY;
`ifdef	FORMAL
		// {{{
		reg			fa1_vlast_locked, fa2_vlast_locked;
		reg	[LGFRAME-1:0]	f_a1_xpos, f_a1_ypos;
		reg	[LGFRAME-1:0]	f_a2_xpos, f_a2_ypos;

		// fa1_vlast_locked
		// {{{
		initial	fa1_vlast_locked = !OPT_TUSER_IS_SOF;
		if (OPT_TUSER_IS_SOF)
		begin
			always @(posedge S_VID_ACLK)
			if (!S_VID_ARESETN)
				fa1_vlast_locked <= 1'b0;
			else if (p_valid && p_step)
				fa1_vlast_locked <= fp_vlast_locked;
		end else begin
			always @(*)
				assert(fa1_vlast_locked);
		end
		// }}}

		// fa2_vlast_locked
		// {{{
		initial	fa2_vlast_locked = !OPT_TUSER_IS_SOF;
		if (OPT_TUSER_IS_SOF)
		begin
			always @(posedge S_VID_ACLK)
			if (!S_VID_ARESETN)
				fa2_vlast_locked <= 1'b0;
			else if (a1_valid && a1_step)
				fa2_vlast_locked <= fa1_vlast_locked;
		end else begin
			always @(*)
				assert(fa2_vlast_locked);
		end
		// }}}

		// fm_vlast_locked
		// {{{
		initial	fm_vlast_locked = !OPT_TUSER_IS_SOF;
		if (OPT_TUSER_IS_SOF)
		begin
			always @(posedge S_VID_ACLK)
			if (!S_VID_ARESETN)
				fm_vlast_locked <= 1'b0;
			else if (!M_AXIS_TVALID || M_AXIS_TREADY)
				fm_vlast_locked <= fa2_vlast_locked;
		end else begin
			always @(*)
				assert(fm_vlast_locked);
		end
		// }}}

		// Count f_a1_xpos, and f_a1_ypos
		// {{{
		initial	f_a1_xpos = 0;
		initial	f_a1_ypos = 0;
		always @(posedge S_VID_ACLK)
		if (!S_VID_ARESETN)
		begin
			f_a1_xpos <= 0;
			f_a1_ypos <= 0;
		end else if (a1_valid && a1_step)
		begin
			f_a1_xpos <= fp_xpos;
			f_a1_ypos <= fp_ypos;
		end

		always @(*)
		begin
			assert(f_a1_xpos < f_pixels_per_line);
			assert(f_a1_ypos < f_lines_per_frame);
			assert(!a1_valid
				|| ((OPT_TUSER_IS_SOF ? a1_tlast : a1_tuser)
					== (f_a1_xpos == f_pixels_per_line-1)));
			if (OPT_TUSER_IS_SOF)
			begin
				assert(!a1_valid || a1_tuser == (f_a1_xpos == 0 && f_a1_ypos == 0));
			end else if (a1_valid && fa1_vlast_locked)
			begin
				assert(a1_tlast == (a1_tuser && f_a1_ypos == f_lines_per_frame-1));
			end else if (a1_valid)
				assert(!a1_tlast);
		end

		always @(*)
		if (!a1_valid) // && !vskd_valid)
		begin
			assert(f_a1_xpos == fp_xpos);
			assert(f_a1_ypos == fp_ypos);
		end else if (fp_xpos > 0)
		begin
			assert(f_a1_xpos + 1 == fp_xpos);
			assert(f_a1_ypos == fp_ypos);
		end else if (fp_ypos > 0)
		begin
			assert(f_a1_xpos == f_pixels_per_line-1);
			assert(f_a1_ypos + 1 == fp_ypos);
		end else begin
			assert(f_a1_xpos == f_pixels_per_line-1);
			assert(f_a1_ypos == f_lines_per_frame-1);
		end
		// }}}

		// Count f_a2_xpos, and f_a2_ypos
		// {{{
		initial	f_a2_xpos = 0;
		initial	f_a2_ypos = 0;
		always @(posedge S_VID_ACLK)
		if (!S_VID_ARESETN)
		begin
			f_a2_xpos <= 0;
			f_a2_ypos <= 0;
		end else if (a2_valid && a2_step)
		begin
			f_a2_xpos <= f_a1_xpos;
			f_a2_ypos <= f_a1_ypos;
		end

		always @(*)
		begin
			assert(f_a2_xpos < f_pixels_per_line);
			assert(f_a2_ypos < f_lines_per_frame);
			assert(!a2_valid
				|| ((OPT_TUSER_IS_SOF ? a2_tlast : a2_tuser)
					== (f_a2_xpos == f_pixels_per_line-1)));
			if (OPT_TUSER_IS_SOF)
			begin
				assert(!a2_valid || a2_tuser == (f_a2_xpos == 0 && f_a2_ypos == 0));
			end else if (a2_valid && fa2_vlast_locked)
			begin
				assert(a2_tlast == (a2_tuser && f_a2_ypos == f_lines_per_frame-1));
			end else if (a2_valid)
				assert(!a2_tlast);
		end

		always @(*)
		if (!a2_valid) // && !vskd_valid)
		begin
			assert(f_a2_xpos == f_a1_xpos);
			assert(f_a2_ypos == f_a1_ypos);
		end else if (f_a1_xpos > 0)
		begin
			assert(f_a2_xpos + 1 == f_a1_xpos);
			assert(f_a2_ypos == f_a1_ypos);
		end else if (f_a1_ypos > 0)
		begin
			assert(f_a2_xpos == f_pixels_per_line-1);
			assert(f_a2_ypos + 1 == f_a1_ypos);
		end else begin
			assert(f_a2_xpos == f_pixels_per_line-1);
			assert(f_a2_ypos == f_lines_per_frame-1);
		end
		// }}}

		// Relate f_a2_* to M_AXIS_*
		// {{{
		always @(posedge gbl_clk)
		if (f_past_valid_vid)
		begin
			if (!M_AXIS_TVALID)
			begin
				assert(f_a2_xpos == M_AXIS_XPOS);
				assert(f_a2_ypos == M_AXIS_YPOS);
			end else if (f_a2_xpos != 0)
			begin
				assert(f_a2_xpos == M_AXIS_XPOS + 1);
				assert(f_a2_ypos == M_AXIS_YPOS);
			end else if (f_a2_ypos > 0)
			begin
				assert(M_AXIS_XPOS == f_pixels_per_line-1);
				assert(f_a2_ypos == M_AXIS_YPOS + 1);
			end else begin
				assert(M_AXIS_XPOS == f_pixels_per_line-1);
				assert(M_AXIS_YPOS == f_lines_per_frame-1);
			end
		end
		// }}}

		// Initial conditions
		// {{{
		always @(*)
		if (!f_past_valid_vid)
		begin
			assert(f_vskd_locked    != OPT_TUSER_IS_SOF);
			assert(fp_vlast_locked  != OPT_TUSER_IS_SOF);
			assert(fa1_vlast_locked != OPT_TUSER_IS_SOF);
			assert(fa2_vlast_locked != OPT_TUSER_IS_SOF);
			assert(fm_vlast_locked  != OPT_TUSER_IS_SOF);

			assert(f_vskd_xpos == 0);
			assert(f_vskd_ypos == 0);
			assert(fp_xpos    == 0);
			assert(fp_ypos    == 0);
			assert(f_a1_xpos   == 0);
			assert(f_a1_ypos   == 0);
			assert(f_a2_xpos   == 0);
			assert(f_a2_ypos   == 0);
			assert(M_AXIS_XPOS == 0);
			assert(M_AXIS_YPOS == 0);
		end
		// }}}
		// }}}
`endif
		// }}}
	end else begin : NO_ALPHA_CHANNEL
		// {{{
		reg			M_AXIS_HLAST, M_AXIS_VLAST, M_AXIS_SOF;
		// M_AXIS_TVALID
		// {{{
		initial	M_AXIS_TVALID = 1'b0;
		always @(posedge S_VID_ACLK)
		if (!S_VID_ARESETN)
			M_AXIS_TVALID <= 1'b0;
		else if (!M_AXIS_TVALID || M_AXIS_TREADY)
			M_AXIS_TVALID <= p_valid;
		// }}}

		// M_AXIS_SOF, M_AXIS_HLAST, M_AXIS_VLAST
		// {{{
		initial	{ M_AXIS_SOF, M_AXIS_HLAST, M_AXIS_VLAST } = 3'b100;
		always @(posedge S_VID_ACLK)
		if (!M_AXIS_TVALID || M_AXIS_TREADY)
			{ M_AXIS_SOF, M_AXIS_HLAST, M_AXIS_VLAST } <= { p_sof, p_hlast, p_vlast };
		// }}}

		if (OPT_TUSER_IS_SOF)
		begin
			always @(*)
				M_AXIS_TUSER = M_AXIS_SOF;
			always @(*)
				M_AXIS_TLAST = M_AXIS_HLAST;
		end else begin
			always @(*)
				M_AXIS_TUSER = M_AXIS_HLAST;
			always @(*)
				M_AXIS_TLAST = M_AXIS_HLAST && M_AXIS_VLAST;
		end

		// M_AXIS_TDATA
		// {{{
		if (ALPHA_BITS == 0)
		begin
			always @(posedge S_VID_ACLK)
			if (p_step)
			begin
				if (in_sprite)
					M_AXIS_TDATA <= spritepix[3*BPP-1:0];
				else
					M_AXIS_TDATA <= p_data;
			end
		end else // if (ALPHA_BITS == 1)
		begin
			always @(posedge S_VID_ACLK)
			if (p_step)
			begin
				if (in_sprite && spritepix[3*BPP])
					M_AXIS_TDATA <= spritepix[3*BPP-1:0];
				else
					M_AXIS_TDATA <= p_data;
			end
		end
		// }}}

		// Pipeline contol: vskd_ready && p_step
		// {{{
		assign	vskd_ready = p_step || !p_valid;
		assign	p_step = !M_AXIS_TVALID || M_AXIS_TREADY;
		// }}}
`ifdef	FORMAL
		// fm_vlast_locked
		// {{{
		initial	fm_vlast_locked = !OPT_TUSER_IS_SOF;
		if (OPT_TUSER_IS_SOF)
		begin
			always @(posedge S_VID_ACLK)
			if (!S_VID_ARESETN)
				fm_vlast_locked <= 1'b0;
			else if (!M_AXIS_TVALID || M_AXIS_TREADY)
				fm_vlast_locked <= fp_vlast_locked;
		end else begin
			always @(*)
				assert(fm_vlast_locked);
		end
		// }}}

		// Relate f_p_* to M_AXIS_*
		// {{{
		always @(posedge gbl_clk)
		if (f_past_valid_vid)
		begin
			if (!M_AXIS_TVALID)
			begin
				assert(fp_xpos == M_AXIS_XPOS);
				assert(fp_ypos == M_AXIS_YPOS);
			end else if (fp_xpos != 0)
			begin
				assert(fp_xpos == M_AXIS_XPOS + 1);
				assert(fp_ypos == M_AXIS_YPOS);
			end else if (fp_ypos > 0)
			begin
				assert(M_AXIS_XPOS == f_pixels_per_line-1);
				assert(fp_ypos == M_AXIS_YPOS + 1);
			end else begin
				assert(M_AXIS_XPOS == f_pixels_per_line-1);
				assert(M_AXIS_YPOS == f_lines_per_frame-1);
			end
		end
		// }}}

		// Initial conditions
		// {{{
		always @(*)
		if (!f_past_valid_vid)
		begin
			assert(f_vskd_locked   != OPT_TUSER_IS_SOF);
			assert(fp_vlast_locked != OPT_TUSER_IS_SOF);
			assert(fm_vlast_locked != OPT_TUSER_IS_SOF);

			assert(f_vskd_xpos == 0);
			assert(f_vskd_ypos == 0);
			assert(fp_xpos    == 0);
			assert(fp_ypos    == 0);
			assert(M_AXIS_XPOS == 0);
			assert(M_AXIS_YPOS == 0);
		end
		// }}}
`endif
		// }}}
	end endgenerate

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
	reg	fp_locked;
	wire	fp_known, fp_hlast, fp_vlast, fp_sof;


	initial	f_past_valid = 0;
	always @(posedge gbl_clk)
		f_past_valid <= 1;

	initial	f_past_valid_bus = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid_bus <= 1;

	initial	f_past_valid_vid = 0;
	always @(posedge S_VID_ACLK)
		f_past_valid_vid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Clock/reset assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_CKDEPTH = 5;
	reg	[F_CKDEPTH-1:0]	r_axi_aclk_sreg, r_vid_aclk_sreg,
				axi_edges,       vid_edges,
				axi_aclk_sreg,   vid_aclk_sreg;
	reg			rose_axi_aclk, rose_vid_aclk;

	always @(*)
	begin
		axi_aclk_sreg = { r_axi_aclk_sreg[F_CKDEPTH-2:0], S_AXI_ACLK };
		vid_aclk_sreg = { r_vid_aclk_sreg[F_CKDEPTH-2:0], S_VID_ACLK };

		rose_axi_aclk = S_AXI_ACLK && !r_axi_aclk_sreg[0];
		rose_vid_aclk = S_VID_ACLK && !r_vid_aclk_sreg[0];

		axi_edges = (r_axi_aclk_sreg[F_CKDEPTH-2:0]&(~r_axi_aclk_sreg[F_CKDEPTH-1:1]));
		vid_edges = (r_vid_aclk_sreg[F_CKDEPTH-2:0]&(~r_vid_aclk_sreg[F_CKDEPTH-1:1]));
	end

	always @(posedge gbl_clk)
	begin
		r_axi_aclk_sreg <= axi_aclk_sreg;
		r_vid_aclk_sreg <= vid_aclk_sreg;
	end

	// Assume the design always starts in reset
	// {{{
	always @(*)
	if (!f_past_valid)
	begin
		assume(!S_AXI_ARESETN);
		assume(!S_VID_ARESETN);
	end
	// }}}

	// The bus will not be reset without resetting the video
	// {{{
	always @(*)
	if (!S_AXI_ARESETN)
		assume(!S_VID_ARESETN);
	// }}}

	// AXI Clk assumption: assume it's not stopped
	// {{{
	always @(posedge gbl_clk)
	if (axi_edges == 0)
		assume(S_AXI_ACLK != r_axi_aclk_sreg[0]);
	// }}}

	// Video Clk assumption: assume it's not stopped
	// {{{
	always @(posedge gbl_clk)
	if (vid_edges == 0)
		assume(S_VID_ACLK != r_vid_aclk_sreg[0]);
	// }}}

	// AXI signals are synchronous with the AXI clock
	// {{{
	always @(posedge gbl_clk)
	if (f_past_valid && !$rose(S_AXI_ACLK))
	begin
		// {{{
		assume(!$rose(S_AXI_ARESETN));

		assume($stable(S_AXI_AWVALID));
		assume($stable(S_AXI_AWADDR));
		assume($stable(S_AXI_AWPROT));

		assume($stable(S_AXI_WVALID));
		assume($stable(S_AXI_WDATA));
		assume($stable(S_AXI_WSTRB));

		assume($stable(S_AXI_ARVALID));
		assume($stable(S_AXI_ARADDR));
		assume($stable(S_AXI_ARPROT));

		assume($stable(S_AXI_BREADY));
		assume($stable(S_AXI_RREADY));
		// }}}
	end else if (f_past_valid && $rose(S_AXI_ACLK))
	begin
		if (!$past(S_AXI_ARESETN))
		begin
			assume(!S_AXI_AWVALID);
			assume(!S_AXI_WVALID);
			assume(!S_AXI_ARVALID);
		end
	end
	// }}}

	always @(*)
	if (!f_past_valid)
	begin
		assume(!S_AXI_AWVALID);
		assume(!S_AXI_WVALID);
		assume(!S_AXI_ARVALID);
		assume(!S_AXIS_TVALID);
	end

	reg					past_s_axi_aresetn;

	reg					past_s_axi_awvalid;
	reg	[C_AXI_ADDR_WIDTH-1:0]		past_s_axi_awaddr;
	reg	[2:0]				past_s_axi_awprot;
	reg	[BPP-1:0]			past_s_axi_awdata;

	reg					past_s_axi_wvalid;
	reg	[C_AXI_DATA_WIDTH-1:0]		past_s_axi_wdata;
	reg	[C_AXI_DATA_WIDTH/8-1:0]	past_s_axi_wstrb;

	reg					past_s_axi_arvalid;
	reg	[C_AXI_ADDR_WIDTH-1:0]		past_s_axi_araddr;
	reg	[2:0]				past_s_axi_arprot;
	reg	[BPP-1:0]			past_s_axi_ardata;

	always @(posedge gbl_clk)
	begin
		past_s_axi_aresetn <= S_AXI_ARESETN;

		past_s_axi_awvalid <= S_AXI_AWVALID;
		past_s_axi_awaddr  <= S_AXI_AWADDR;
		past_s_axi_awprot  <= S_AXI_AWPROT;
		past_s_axi_wvalid  <= S_AXI_WVALID;
		past_s_axi_wdata   <= S_AXI_WDATA;
		past_s_axi_wstrb   <= S_AXI_WSTRB;
		past_s_axi_arvalid <= S_AXI_ARVALID;
		past_s_axi_araddr  <= S_AXI_ARADDR;
		past_s_axi_arprot  <= S_AXI_ARPROT;
	end

	always @(*)
	if (f_past_valid && !rose_axi_aclk)
	begin
		assume(!past_s_axi_aresetn || S_AXI_ARESETN);

		assume(past_s_axi_awvalid == S_AXI_AWVALID);
		assume(past_s_axi_awaddr  == S_AXI_AWADDR);
		assume(past_s_axi_awprot  == S_AXI_AWPROT);
		assume(past_s_axi_wvalid  == S_AXI_WVALID);
		assume(past_s_axi_wdata   == S_AXI_WDATA);
		assume(past_s_axi_wstrb   == S_AXI_WSTRB);
		assume(past_s_axi_arvalid == S_AXI_ARVALID);
		assume(past_s_axi_araddr  == S_AXI_ARADDR);
		assume(past_s_axi_arprot  == S_AXI_ARPROT);
	end

	reg			past_s_vid_aresetn;
	reg			past_s_vid_tvalid;
	reg	[BPP-1:0]	past_s_vid_tdata;
	reg			past_s_vid_tuser;
	reg			past_s_vid_tlast;

	always @(posedge gbl_clk)
	begin
		past_s_vid_aresetn <= S_VID_ARESETN;
		past_s_vid_tvalid <= S_AXIS_TVALID;
		past_s_vid_tdata  <= S_AXIS_TDATA;
		past_s_vid_tuser  <= S_AXIS_TUSER;
		past_s_vid_tlast  <= S_AXIS_TLAST;
	end

	always @(*)
	if (f_past_valid && !rose_vid_aclk)
	begin
		assume(!past_s_vid_aresetn || S_VID_ARESETN);
		assume(past_s_vid_tvalid == S_AXIS_TVALID);
		assume(past_s_vid_tdata  == S_AXIS_TDATA);
		assume(past_s_vid_tuser  == S_AXIS_TUSER);
		assume(past_s_vid_tlast  == S_AXIS_TLAST);
	end

	always @(posedge gbl_clk)
	if (f_past_valid && !$rose(S_VID_ACLK))
	begin
		// {{{
		assume(!$rose(S_VID_ARESETN));

		assume($stable(S_AXIS_TVALID));
		assume($stable(M_AXIS_TREADY));
		assume($stable(S_AXIS_TDATA));
		assume($stable(S_AXIS_TUSER));
		assume($stable(S_AXIS_TLAST));
		//
		if (S_VID_ARESETN)
		begin
			assert($stable(M_AXIS_TVALID));
			assert($stable(S_AXIS_TREADY));
			assert($stable(M_AXIS_TDATA));
			assert($stable(M_AXIS_TUSER));
			assert($stable(M_AXIS_TLAST));
		end
		// }}}
	end else if (f_past_valid && $rose(S_VID_ACLK))
	begin
		if (!$past(S_VID_ARESETN))
			assume(!S_AXIS_TVALID);
	end

	// }}}
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

	//
	// AXI stream checks
	// {{{
	always @(posedge S_VID_ACLK)
	if (!f_past_valid_vid || $past(!S_VID_ARESETN))
		assume(!S_AXIS_TVALID);
	else if ($past(S_AXIS_TVALID&&!S_AXIS_TREADY))
		assume(S_AXIS_TVALID && $stable({ S_AXIS_TUSER, S_AXIS_TLAST,
				S_AXIS_TDATA }));

	always @(posedge S_VID_ACLK)
	if (!f_past_valid_vid || $past(!S_VID_ARESETN))
		assert(!p_valid);

	always @(posedge S_VID_ACLK)
	if (!f_past_valid_vid || $past(!S_VID_ARESETN))
	begin
		assert(!M_AXIS_TVALID);
	end else if ($past(M_AXIS_TVALID&&!M_AXIS_TREADY))
		assert(M_AXIS_TVALID && $stable({ M_AXIS_TUSER, M_AXIS_TLAST,
				M_AXIS_TDATA }));
	// }}}

	// Count S_AXIS_XPOS and S_AXIS_YPOS
	// {{{
	faxivideo #(
		.LGDIM(LGFRAME), .PW(BPP), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
	) fSVID (
		// {{{
		.i_clk(S_VID_ACLK), .i_reset_n(S_VID_ARESETN),
		//
		.S_VID_TVALID(S_AXIS_TVALID), .S_VID_TREADY(S_AXIS_TREADY),
		.S_VID_TDATA(S_AXIS_TDATA), .S_VID_TLAST(S_AXIS_TLAST),
			.S_VID_TUSER(S_AXIS_TUSER),
		//
		.i_width(f_pixels_per_line), .i_height(f_lines_per_frame),
		.o_xpos(S_AXIS_XPOS), .o_ypos(S_AXIS_YPOS),
			.f_known_height(fs_known),
		.o_hlast(fs_hlast), .o_vlast(fs_vlast), .o_sof(fs_sof)
		// }}}
	);

	always @(*)
	begin
		assume(!S_AXIS_TVALID || S_AXIS_HLAST == fs_hlast);

		if (OPT_TUSER_IS_SOF)
		begin
			assume(!S_AXIS_TVALID || S_AXIS_SOF == fs_sof);
		end else begin
			assume(!S_AXIS_TVALID || S_AXIS_VLAST == (fs_vlast && fs_hlast));
		end
	end

	always @(posedge S_VID_ACLK)
	begin
		if (!OPT_TUSER_IS_SOF)
			assert(S_AXIS_SOF == (S_AXIS_XPOS == 0 && S_AXIS_YPOS == 0));

		if (fs_known && (S_AXIS_XPOS != 0 || S_AXIS_YPOS != 0))
			assert(f_vlast_locked);
	end
	// }}}

	// Count f_vskd_xpos, and f_vskd_ypos
	// {{{
	wire	fvskd_known, fvskd_sof;
	generate if (OPT_SKIDBUFFER)
	begin : GEN_VSKD_COUNTS
		// {{{
		wire			fvskd_vlast, fvskd_hlast;

		faxivideo #(
			// {{{
			.LGDIM(LGFRAME), .PW(BPP),
			.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
			// }}}
		) fvskd (
			// {{{
			.i_clk(S_VID_ACLK), .i_reset_n(S_VID_ARESETN),
			//
			.S_VID_TVALID(vskd_valid), .S_VID_TREADY(vskd_ready),
			.S_VID_TDATA(vskd_data),
				.S_VID_TLAST(OPT_TUSER_IS_SOF ? vskd_hlast : (vskd_hlast && vskd_vlast)),
				.S_VID_TUSER((OPT_TUSER_IS_SOF) ? vskd_sof : vskd_hlast),
			//
			.i_width(f_pixels_per_line), .i_height(f_lines_per_frame),
			.o_xpos(f_vskd_xpos), .o_ypos(f_vskd_ypos),
				.f_known_height(fvskd_known),
			.o_hlast(fvskd_hlast), .o_vlast(fvskd_vlast),
				.o_sof(fvskd_sof)
			// }}}
		);

		// Bounds checking on f_vskd*, vskd_hlast and vskd_sof checks
		// {{{
		always @(posedge S_VID_ACLK)
		if (S_AXI_ARESETN)
		begin
			assert(!vskd_valid || vskd_hlast == fvskd_hlast);
			assert(!vskd_valid || vskd_sof   == fvskd_sof);
			assert(!vskd_valid || !f_vskd_locked
				|| vskd_vlast == (fvskd_vlast && fvskd_hlast));
			if (f_vskd_locked)
			begin
				if (!fvskd_vlast)
				begin
					assert(!vskd_vlast || !vskd_valid);
				end else if (vskd_hlast)
					assert(vskd_vlast == fvskd_hlast || !vskd_valid);
			end else if (vskd_valid)
				assert(!vskd_vlast);
		end
		// }}}

		// Related f_vskd_* to S_AXIS_*
		// {{{
		always @(posedge gbl_clk)
		if (S_VID_ARESETN)
		begin
			if (fvskd_known)
			begin
				assert(fs_known);
			end

			if (f_vskd_locked)
			begin
				assert(fvskd_known);
			end else if (fvskd_known)
			begin
				assert(f_vskd_xpos <= 2);
				assert(f_vskd_ypos == 0);
			end

			if (vskd_valid&& !S_AXIS_TREADY && (S_AXIS_XPOS == 0)
						&& (S_AXIS_YPOS==0))
				assert(fs_known);

			if (fs_known && !fvskd_known)
			begin
				assert(vskd_valid);
				assert(fvskd_hlast);
				assert(fvskd_vlast);
			end
		end
		
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
		assign	f_vskd_xpos = S_AXIS_XPOS;
		assign	f_vskd_ypos = S_AXIS_YPOS;
		assign	fvskd_known = fs_known;
		assign	fvskd_sof   = fs_sof;

		always @(posedge S_VID_ACLK)
		if (S_AXI_ARESETN && vskd_valid)
		begin
			assert(vskd_hlast == fs_hlast);
			if (OPT_TUSER_IS_SOF)
			begin
				assert(vskd_sof   == fs_sof);
			end else if (f_vskd_locked)
			begin
				assert(vskd_vlast == (fs_vlast && fs_hlast));
			end
		end
	end endgenerate
	// }}}

	// Count fp_xpos, and fp_ypos
	// {{{
	faxivideo #(
		.LGDIM(LGFRAME), .PW(BPP), .OPT_TUSER_IS_SOF(1'b0)
	) fpvid (
		// {{{
		.i_clk(S_VID_ACLK), .i_reset_n(S_VID_ARESETN),
		//
		.S_VID_TVALID(p_valid), .S_VID_TREADY(p_step),
		.S_VID_TDATA(p_data), .S_VID_TLAST(
			(fp_known) ? (p_hlast && p_vlast)
				: ((fp_xpos == f_pixels_per_line-1)
					&&(fp_ypos == f_lines_per_frame-1))),
			.S_VID_TUSER(p_hlast),
		//
		.i_width(f_pixels_per_line), .i_height(f_lines_per_frame),
		.o_xpos(fp_xpos), .o_ypos(fp_ypos),
			.f_known_height(fp_known),
		.o_hlast(fp_hlast), .o_vlast(fp_vlast), .o_sof(fp_sof)
		// }}}
	);

	always @(posedge gbl_clk)
	if (S_VID_ARESETN)
	begin
		assert(!p_valid || p_hlast == fp_hlast);
		assert(!p_valid || !fp_known || p_sof == fp_sof);

		if (fp_known)
		begin
			assert(fvskd_known);
		end else if (fvskd_known)
		begin
			assert(fvskd_sof || (p_valid && p_sof));
			assert(fp_vlast && fp_hlast);
			assert(!OPT_TUSER_IS_SOF || !fp_vlast_locked);
		end else begin
			assert(fp_ypos <= f_vskd_ypos);
		end

		if (fp_vlast_locked) // || !OPT_TUSER_IS_SOF is implied
		begin
			assert(f_vskd_locked);
		end else if (f_vskd_locked)
		begin
			assert(fp_xpos == 1); // Was (p_valid ? 0:1));
			assert(fp_ypos == 0);
			assert(fp_known);
		end

		/*
		if (OPT_TUSER_IS_SOF)
		begin
			if (fp_vlast_locked)
			begin
				assert(fp_known);
			end else if (fp_known)
			begin
				assert(fp_ypos==0);
				assert(fp_xpos == (p_valid ? 0:1));
			end
			// assert(fp_vlast_locked == fp_known);
		end else
			assert(fp_vlast_locked);
		*/

		if (fp_xpos > (p_valid ? 0:1) || fp_ypos != 0)
			assert(!p_sof);

		if (fp_vlast_locked && p_valid)
		begin
			assert(p_vlast == (p_hlast && fp_vlast));
		end else if (p_valid)
			assert(!p_vlast);
	end

	always @(posedge gbl_clk)
	if (!p_valid) // && !vskd_valid)
	begin
		assert(fp_xpos == f_vskd_xpos);
		assert(fp_ypos == f_vskd_ypos);
	end else if (f_vskd_xpos > 0)
	begin
		assert(fp_xpos + 1 == f_vskd_xpos);
		assert(fp_ypos == f_vskd_ypos);
	end else if (f_vskd_ypos > 0)
	begin
		assert(fp_xpos == f_pixels_per_line-1);
		assert(fp_ypos + 1 == f_vskd_ypos);
	end else begin
		assert(fp_xpos == f_pixels_per_line-1);
		assert(fp_ypos == f_lines_per_frame-1);
	end
	// }}}

	// Count M_AXIS_XPOS and M_AXIS_YPOS
	// {{{
	faxivideo #(
		.LGDIM(LGFRAME), .PW(BPP), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
	) fMVID (
		// {{{
		.i_clk(S_VID_ACLK), .i_reset_n(S_VID_ARESETN),
		//
		.S_VID_TVALID(M_AXIS_TVALID), .S_VID_TREADY(M_AXIS_TREADY),
		.S_VID_TDATA(M_AXIS_TDATA), .S_VID_TLAST(M_AXIS_TLAST),
			.S_VID_TUSER(M_AXIS_TUSER),
		//
		.i_width(f_pixels_per_line), .i_height(f_lines_per_frame),
		.o_xpos(M_AXIS_XPOS), .o_ypos(M_AXIS_YPOS),
			.f_known_height(fM_known),
		.o_hlast(fM_hlast), .o_vlast(fM_vlast), .o_sof(fM_sof)
		// }}}
	);

	// Limits, and M_AXIS_HLAST, M_AXIS_SOF
	// {{{
	always @(posedge gbl_clk)
	if (S_VID_ARESETN && M_AXIS_TVALID && !OPT_TUSER_IS_SOF)
	begin
		if (!fm_vlast_locked)
			assert(!M_AXIS_TLAST);
	end

	always @(posedge gbl_clk)
	if (S_VID_ARESETN && OPT_TUSER_IS_SOF)
	begin
		if (fM_known)
		begin
			assert(fp_known);
		else if (fp_known)
		begin
			assert(M_AXIS_TVALID
				&& (M_AXIS_XPOS == f_pixels_per_line-1)
				&& (M_AXIS_YPOS == f_lines_per_frame-1));
		end

		if (fM_known)
			assert(fm_vlast_locked || ((M_AXIS_XPOS <= (M_AXIS_TVALID ? 0:1)) && (M_AXIS_YPOS == 0)));
		if (!fM_known && M_AXIS_XPOS > (M_AXIS_TVALID ? 0:1))
			assert(!M_AXIS_TUSER);

		if (fm_vlast_locked)
		begin
			assert(fM_known);
			assert(fp_vlast_locked);
		end else if (fp_vlast_locked)
		begin
			assert(fM_known);
			assert(M_AXIS_YPOS == 0);
			assert(M_AXIS_XPOS <= 2);
		end
	end
	// }}}
	// }}}

	// frame_x and frame_y
	// {{{
	always @(posedge gbl_clk)
	begin
		if (!OPT_TUSER_IS_SOF || fp_locked)
			assert(frame_y < f_lines_per_frame);

		assert(frame_x < f_pixels_per_line);
		assert(frame_x == f_vskd_xpos);
		if (OPT_TUSER_IS_SOF && f_vskd_locked)
			assert(fs_known);
		if (fp_locked)
			assert(frame_y == f_vskd_ypos);
	end
	// }}}

	generate if (OPT_TUSER_IS_SOF)
	begin : CHECK_VLAST
		// {{{
		reg	r_vskd_locked, p_vlast_locked, vlast_locked;

		// f_vskd_locked
		// {{{
		if (OPT_SKIDBUFFER)
		begin
			initial	r_vskd_locked = 1'b0;
			always @(posedge S_VID_ACLK)
			if (!S_VID_ARESETN)
				r_vskd_locked <= 1'b0;
			else if (vskd_valid && vskd_ready)
				r_vskd_locked <= f_vlast_locked;

			assign	f_vskd_locked = r_vskd_locked;
		end else begin
			assign	f_vskd_locked = f_vlast_locked;
		end
		// }}}

		// fp_vlast_locked
		// {{{
		initial	p_vlast_locked = 1'b0;
		always @(posedge S_VID_ACLK)
		if (!S_VID_ARESETN)
			p_vlast_locked <= 1'b0;
		else if (vskd_valid && vskd_ready)
			p_vlast_locked <= f_vskd_locked;

		assign	fp_vlast_locked = p_vlast_locked;
		// }}}

		always @(posedge gbl_clk)
		if (S_VID_ARESETN)
		case({ f_vlast_locked, f_vskd_locked, fp_vlast_locked, fm_vlast_locked})
		4'b0000: begin end
		4'b1000: begin
			if (S_AXIS_TREADY || !OPT_SKIDBUFFER)
			begin
				assert(S_AXIS_XPOS == 1);
				assert(f_vskd_xpos == S_AXIS_XPOS);
			end else begin
				assert(S_AXIS_XPOS == 2);
				assert(f_vskd_xpos == 1);
			end
			assert(S_AXIS_YPOS == 0);
			assert(f_vskd_ypos == 0);
			end
		4'b1100: begin
			assert(f_vskd_xpos == 2);
			assert(f_vskd_ypos == 0);
			// assert(p_sof);
			end
		4'b1110: begin end
		4'b1111: begin end
		default: assert(0);
		endcase

		always @(*)
		if (fp_locked)
			assert(frame_y < f_lines_per_frame);
		// }}}
	end else begin : ASSUME_VLAST_VALID
		// {{{
		assign	f_vlast_locked  = 1'b1;
		assign	f_vskd_locked   = 1'b1;
		assign	fp_vlast_locked = 1'b1;
		// }}}
	end endgenerate

	initial	fp_locked = !OPT_TUSER_IS_SOF;
	always @(posedge S_VID_ACLK)
	if (!S_VID_ARESETN)
		fp_locked <= !OPT_TUSER_IS_SOF;
	else if (vskd_valid && vskd_ready && s_vlast)
		fp_locked <= 1;

	always @(*)
	if (S_VID_ARESETN)
	begin
		if (!OPT_TUSER_IS_SOF)
		begin
			assert(fp_locked);
		end else if (!f_vskd_locked || !fp_vlast_locked)
			assert(!fp_locked);
	end

	always @(*)
	if (S_VID_ARESETN && fp_locked)
	begin
		assert(sprite_x <= XSIZE);
		assert(sprite_y <= YSIZE);

		if (frame_y < this_top)
		begin
			assert(maddr == 0);
		end else if (in_sprite_y && XSIZE == (1<<$clog2(XSIZE)))
		begin
			if (frame_x >= this_left + XSIZE)
			begin
				assert(maddr == (sprite_y << $clog2(XSIZE)) + XSIZE-1);
			end else
				assert(maddr == (sprite_y << $clog2(XSIZE)) + sprite_x);
		end

		assert(in_sprite_x == ((frame_x >= this_left)
					&& (frame_x < this_left + XSIZE)));
		assert(in_sprite_y == ((frame_y >= this_top)
					&& (frame_y < this_top + YSIZE)));

		if (in_sprite_x)
		begin
			assert(sprite_x == (frame_x - this_left));
		end else if (frame_x < this_left)
		begin
			assert(sprite_x == 0);
		end else
			assert(sprite_x == XSIZE);

		if (in_sprite_y)
		begin
			assert(sprite_y == (frame_y - this_top));
		end else // if (!OPT_TUSER_IS_SOF)
		begin
			assert((sprite_y != 0) ==(frame_y >= this_top + YSIZE));
		end
		/*
		else if (frame_x > 1 || f_vskd_locked
				|| frame_y < f_lines_per_frame)
			assert(1 || (sprite_y != 0) ==(frame_y >= this_top + YSIZE));
		*/
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
	always @(posedge S_VID_ACLK)
	if (!S_VID_ARESETN)
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
	always @(posedge S_VID_ACLK)
	if (!S_VID_ARESETN)
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
	always @(posedge S_VID_ACLK)
	if (!S_VID_ARESETN)
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

`ifdef	VERIFIC
	cover property (@(posedge S_VID_ACLK)
		S_VID_ARESETN && S_AXIS_TREADY && S_AXIS_TVALID throughout (
			!S_AXIS_HLAST
			##1 S_AXIS_HLAST
			##1 !S_AXIS_HLAST
			##1 S_AXIS_HLAST && S_AXIS_VLAST)
		);
`endif
	// }}}
`endif
// }}}
endmodule

