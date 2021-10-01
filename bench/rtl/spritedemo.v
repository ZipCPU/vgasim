////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	spritedemo.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Demonstrates using the modules within the design to read a frame
//		buffer from (block RAM) memory, and send it to a (possibly HDMI)
//	display.  Uses AXI and AXI-stream throughout, control is handled via
//	an AXI-lite interface to the external world.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2021, Gisselquist Technology, LLC
// {{{
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
// `define	HDMI
// }}}
module	spritedemo #(
		// {{{
		parameter AXI_ADDR_WIDTH = 26,
		parameter AXI_DATA_WIDTH = 32,
		parameter AXI_ID_WIDTH = 1,
		parameter AW = AXI_ADDR_WIDTH,
		parameter DW = AXI_DATA_WIDTH,
		parameter IW = AXI_ID_WIDTH,
		//
		parameter	SPRITE_FILE="gtpix.hex",
		//
		parameter C_AXIL_ADDR_WIDTH = 16,
		parameter C_AXIL_DATA_WIDTH = 32
		// parameter AWL = C_AXIL_ADDR_WIDTH,
		// parameter DWL = C_AXIL_ADDR_WIDTH
		// }}}
	) (
		// {{{
		input	wire	i_clk,
		input	wire	i_pixclk,
		input	wire	i_reset,
		// Pixel/video outputs
		// {{{
`ifdef	HDMI
		output	wire	[9:0]	o_hdmi_red,
		output	wire	[9:0]	o_hdmi_grn,
		output	wire	[9:0]	o_hdmi_blu,
`else
		output	wire		o_vga_vsync, o_vga_hsync,
		output	wire	[7:0]	o_vga_red,
		output	wire	[7:0]	o_vga_grn,
		output	wire	[7:0]	o_vga_blu,
`endif
		// }}}
		// AXI-lite control interface
		// {{{
		input	wire					S_AXI_AWVALID,
		output	wire					S_AXI_AWREADY,
		input	wire	[C_AXIL_ADDR_WIDTH-1:0]		S_AXI_AWADDR,
		input	wire	[2:0]				S_AXI_AWPROT,
		//
		input	wire					S_AXI_WVALID,
		output	wire					S_AXI_WREADY,
		input	wire	[C_AXIL_DATA_WIDTH-1:0]		S_AXI_WDATA,
		input	wire	[C_AXIL_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		//
		output	wire					S_AXI_BVALID,
		input	wire					S_AXI_BREADY,
		output	wire	[1:0]				S_AXI_BRESP,
		//
		input	wire					S_AXI_ARVALID,
		output	wire					S_AXI_ARREADY,
		input	wire	[C_AXIL_ADDR_WIDTH-1:0]		S_AXI_ARADDR,
		input	wire	[2:0]				S_AXI_ARPROT,
		//
		output	wire					S_AXI_RVALID,
		input	wire					S_AXI_RREADY,
		output	wire	[C_AXIL_DATA_WIDTH-1:0]		S_AXI_RDATA,
		output	wire	[1:0]				S_AXI_RRESP
		// }}}
		// }}}
	);

	// Register/net declarations
	// {{{
	// Internal AXI-lite interface

	// Video control interface
	// {{{
	wire				axil_vid_awvalid, axil_vid_awready;
	wire	[C_AXIL_ADDR_WIDTH-1:0]	axil_vid_awaddr;
	wire	[2:0]			axil_vid_awprot;
	wire				axil_vid_wvalid, axil_vid_wready;
	wire	[C_AXIL_DATA_WIDTH-1:0]	axil_vid_wdata;
	wire [C_AXIL_DATA_WIDTH/8-1:0]	axil_vid_wstrb;
	wire	[2:0]			axil_vid_awprot;
	wire				axil_vid_bvalid, axil_vid_bready;
	wire	[1:0]			axil_vid_bresp;
	wire				axil_vid_arvalid, axil_vid_arready;
	wire	[C_AXIL_ADDR_WIDTH-1:0]	axil_vid_araddr;
	wire	[2:0]			axil_vid_arprot;
	wire				axil_vid_rvalid, axil_vid_rready;
	wire	[C_AXIL_DATA_WIDTH-1:0]	axil_vid_rdata;
	wire	[1:0]			axil_vid_rresp;
	// }}}

	// Sprite control interface
	// {{{
	wire				axil_sprite_awvalid,axil_sprite_awready;
	wire	[C_AXIL_ADDR_WIDTH-1:0]	axil_sprite_awaddr;
	wire	[2:0]			axil_sprite_awprot;
	wire				axil_sprite_wvalid, axil_sprite_wready;
	wire	[C_AXIL_DATA_WIDTH-1:0]	axil_sprite_wdata;
	wire [C_AXIL_DATA_WIDTH/8-1:0]	axil_sprite_wstrb;
	wire	[2:0]			axil_sprite_awprot;
	wire				axil_sprite_bvalid, axil_sprite_bready;
	wire	[1:0]			axil_sprite_bresp;
	wire				axil_sprite_arvalid,axil_sprite_arready;
	wire	[C_AXIL_ADDR_WIDTH-1:0]	axil_sprite_araddr;
	wire	[2:0]			axil_sprite_arprot;
	wire				axil_sprite_rvalid, axil_sprite_rready;
	wire	[C_AXIL_DATA_WIDTH-1:0]	axil_sprite_rdata;
	wire	[1:0]			axil_sprite_rresp;
	// }}}

	// Internal AXI (not lite) interface
	// {{{
	wire		mem_awready, mem_arready, mem_wready, mem_rready,
			mem_arvalid, mem_bvalid, mem_rvalid, mem_rlast;
	wire [IW-1:0]	mem_arid, mem_bid, mem_rid;
	wire [AW-1:0]	mem_araddr;
	wire [7:0]	mem_arlen;
	wire	[2:0]	mem_arsize;
	wire	[1:0]	mem_arburst;
	wire	[0:0]	mem_arlock;
	wire	[3:0]	mem_arcache;
	wire	[2:0]	mem_arprot;
	wire	[3:0]	mem_arqos;

	wire	[1:0]	mem_rresp, mem_bresp;
	wire [DW-1:0]	mem_rdata;
	// }}}

	// RAM interface
	// {{{
	wire			ram_we, ram_rd;
	reg	[AWW-1:0]	ram_waddr, ram_raddr;
	reg	[DW-1:0]	ram_wdata, ram_rdata;
	reg	[DW/8-1:0]	ram_wstrb;
	reg	[DW-1:0]	ram	[0:(1<<AWW)-1];
	integer			rk;
	// }}}

	// (Unused) clock output generator
	wire	[7:0]	genclk_word;

	// Video stream cut interface
	// {{{
	wire	vid_aclk, vid_reset_n;
	//
	// The video source
	wire		vsrc_tvalid, vsrc_tready;
	wire	[23:0]	vsrc_tdata;
	wire		vsrc_tuser, vsrc_tlast;
	//
	// The video sink
	wire		vsnk_tvalid, vsnk_tready;
	wire	[23:0]	vsnk_tdata;
	wire		vsnk_tuser, vsnk_tlast;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite Crossbar
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	axilxbar #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXIL_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXIL_ADDR_WIDTH),
		.NM(1), .NS(2),
		.SLAVE_ADDR(
			{ { 1'b1, 15'h0 },
			  { 1'b0, 15'h0 } }
		),
		.SLAVE_MASK(
			{ { 1'b1, 15'h0 },
			  { 1'b1, 15'h0 } }
		)
		// }}}
	) u_axilxbar (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		// Incoming interfaces from the various AXI-lite masters
		// {{{
		.S_AXI_AWVALID(S_AXI_AWVALID),
		.S_AXI_AWREADY(S_AXI_AWREADY),
		.S_AXI_AWADDR( S_AXI_AWADDR),
		.S_AXI_AWPROT( S_AXI_AWPROT),
		//
		.S_AXI_WVALID(S_AXI_WVALID),
		.S_AXI_WREADY(S_AXI_WREADY),
		.S_AXI_WDATA( S_AXI_WDATA),
		.S_AXI_WSTRB( S_AXI_WSTRB),
		//
		.S_AXI_BVALID(S_AXI_BVALID),
		.S_AXI_BREADY(S_AXI_BREADY),
		.S_AXI_BRESP( S_AXI_BRESP),
		//
		.S_AXI_ARVALID(S_AXI_ARVALID),
		.S_AXI_ARREADY(S_AXI_ARREADY),
		.S_AXI_ARADDR( S_AXI_ARADDR),
		.S_AXI_ARPROT( S_AXI_ARPROT),
		//
		.S_AXI_RVALID(S_AXI_RVALID),
		.S_AXI_RREADY(S_AXI_RREADY),
		.S_AXI_RDATA( S_AXI_RDATA),
		.S_AXI_RRESP( S_AXI_RRESP),
		// }}}
		// Outgoing interfaces to the various AXI-lite slaves
		// {{{
		.M_AXI_AWVALID({ axil_sprite_awvalid, axil_vid_awvalid }),
		.M_AXI_AWREADY({ axil_sprite_awready, axil_vid_awready }),
		.M_AXI_AWADDR( { axil_sprite_awaddr,  axil_vid_awaddr }),
		.M_AXI_AWPROT( { axil_sprite_awprot,  axil_vid_awprot }),
		//
		.M_AXI_WVALID({ axil_sprite_wvalid, axil_vid_wvalid }),
		.M_AXI_WREADY({ axil_sprite_wready, axil_vid_wready }),
		.M_AXI_WDATA( { axil_sprite_wdata,  axil_vid_wdata }),
		.M_AXI_WSTRB( { axil_sprite_wstrb,  axil_vid_wstrb }),
		//
		.M_AXI_BVALID({ axil_sprite_bvalid, axil_vid_bvalid }),
		.M_AXI_BREADY({ axil_sprite_bready, axil_vid_bready }),
		.M_AXI_BRESP( { axil_sprite_bresp,  axil_vid_bresp }),
		//
		.M_AXI_ARVALID({ axil_sprite_arvalid, axil_vid_arvalid }),
		.M_AXI_ARREADY({ axil_sprite_arready, axil_vid_arready }),
		.M_AXI_ARADDR( { axil_sprite_araddr,  axil_vid_araddr }),
		.M_AXI_ARPROT( { axil_sprite_arprot,  axil_vid_arprot }),
		//
		.M_AXI_RVALID({ axil_sprite_rvalid, axil_vid_rvalid }),
		.M_AXI_RREADY({ axil_sprite_rready, axil_vid_rready }),
		.M_AXI_RDATA( { axil_sprite_rdata,  axil_vid_rdata }),
		.M_AXI_RRESP( { axil_sprite_rresp,  axil_vid_rresp })
		// }}}
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI block RAM controller
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Decode the AXI bus to generate RAM access commands
	// {{{
	demofull #(
		.C_S_AXI_ID_WIDTH(AXI_ID_WIDTH),
		.C_S_AXI_DATA_WIDTH(AXI_DATA_WIDTH),
		.C_S_AXI_ADDR_WIDTH(AXI_ADDR_WIDTH)
	) memcontrol (
		.S_AXI_ACLK(i_clk),
		.S_AXI_ARESETN(!i_reset),
		// AXI interface
		// {{{
		.S_AXI_AWVALID(1'b0),
		.S_AXI_AWREADY(mem_awready),
		.S_AXI_AWID(   mem_arid),
		.S_AXI_AWADDR( mem_araddr),
		.S_AXI_AWLEN(  mem_arlen),
		.S_AXI_AWSIZE( mem_arsize),
		.S_AXI_AWBURST(mem_arburst),
		.S_AXI_AWLOCK( mem_arlock),
		.S_AXI_AWCACHE(mem_arcache),
		.S_AXI_AWPROT( mem_arprot),
		.S_AXI_AWQOS(  mem_arqos),
		//
		.S_AXI_WVALID(1'b0),
		.S_AXI_WREADY(mem_wready),
		.S_AXI_WDATA({(AXI_DATA_WIDTH){1'b0}}),
		.S_AXI_WLAST(1'b0),
		.S_AXI_WSTRB({(AXI_DATA_WIDTH/8){1'b0}}),
		//
		.S_AXI_BVALID(mem_bvalid),
		.S_AXI_BREADY(1'b1),
		.S_AXI_BID(mem_bid),
		.S_AXI_BRESP(mem_bresp),
		//
		.S_AXI_ARVALID(mem_arvalid),
		.S_AXI_ARREADY(mem_arready),
		.S_AXI_ARID(mem_arid),
		.S_AXI_ARADDR(mem_araddr),
		.S_AXI_ARLEN(mem_arlen),
		.S_AXI_ARSIZE(mem_arsize),
		.S_AXI_ARBURST(mem_arburst),
		.S_AXI_ARLOCK(mem_arlock),
		.S_AXI_ARCACHE(mem_arcache),
		.S_AXI_ARPROT(mem_arprot),
		.S_AXI_ARQOS(mem_arqos),
		//
		.S_AXI_RVALID(mem_rvalid),
		.S_AXI_RREADY(mem_rready),
		.S_AXI_RDATA(mem_rdata),
		.S_AXI_RLAST(mem_rlast),
		.S_AXI_RID(mem_rid),
		.S_AXI_RRESP(mem_rresp),
		// }}}
		// Raw/decoded (external) memory interface
		// {{{
		.o_we(ram_we),
		.o_waddr(ram_waddr),
		.o_wdata(ram_wdata),
		.o_wstrb(ram_wstrb),
		.o_rd(ram_rd),
		.o_raddr(ram_raddr),
		.i_rdata(ram_rdata)
		// }}}
	);
	// }}}

	// Issue those commands to the RAM
	// {{{
	localparam	AWW = AW-$clog2(DW/8);

	// initial	$readmemh("slide.hex", ram);
	initial	$readmemh("clr4.hex", ram);

	always @(posedge i_clk)
	for(rk=0; rk<DW/8; rk=rk+1)
	if(ram_we && ram_wstrb[rk])
		ram[ram_waddr][rk*8 +: 8] <= ram_wdata[rk*8 +: 8];

	always @(posedge i_clk)
	if(ram_rd)
		ram_rdata <= ram[ram_raddr];
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI Video controller
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	axivideo #(
		// {{{
		.C_AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(AXI_DATA_WIDTH),
		.C_AXI_ID_WIDTH(AXI_ID_WIDTH),
		.OPT_EXTERNAL(1'b1)
		// }}}
	) video (
		// {{{
		.S_AXI_ACLK(i_clk),
		.S_AXI_ARESETN(!i_reset),
		// AXI-lite control interface
		// {{{
		.S_AXIL_AWVALID(axil_vid_awvalid),
		.S_AXIL_AWREADY(axil_vid_awready),
		.S_AXIL_AWADDR( axil_vid_awaddr[10:0]),
		.S_AXIL_AWPROT( axil_vid_awprot),
		//
		.S_AXIL_WVALID(axil_vid_wvalid),
		.S_AXIL_WREADY(axil_vid_wready),
		.S_AXIL_WDATA( axil_vid_wdata),
		.S_AXIL_WSTRB( axil_vid_wstrb),
		//
		.S_AXIL_BVALID(axil_vid_bvalid),
		.S_AXIL_BREADY(axil_vid_bready),
		.S_AXIL_BRESP( axil_vid_bresp),
		//
		.S_AXIL_ARVALID(axil_vid_arvalid),
		.S_AXIL_ARREADY(axil_vid_arready),
		.S_AXIL_ARADDR( axil_vid_araddr[10:0]),
		.S_AXIL_ARPROT( axil_vid_arprot),
		//
		.S_AXIL_RVALID(axil_vid_rvalid),
		.S_AXIL_RREADY(axil_vid_rready),
		.S_AXIL_RDATA( axil_vid_rdata),
		.S_AXIL_RRESP( axil_vid_rresp),
		// }}}
		// AXI data interface
		// {{{
		.M_AXI_ARVALID(mem_arvalid),
		.M_AXI_ARREADY(mem_arready),
		.M_AXI_ARID(mem_arid),
		.M_AXI_ARADDR(mem_araddr),
		.M_AXI_ARLEN(mem_arlen),
		.M_AXI_ARSIZE(mem_arsize),
		.M_AXI_ARBURST(mem_arburst),
		.M_AXI_ARLOCK(mem_arlock),
		.M_AXI_ARCACHE(mem_arcache),
		.M_AXI_ARPROT(mem_arprot),
		.M_AXI_ARQOS(mem_arqos),
		//
		.M_AXI_RVALID(mem_rvalid),
		.M_AXI_RREADY(mem_rready),
		.M_AXI_RDATA(mem_rdata),
		.M_AXI_RLAST(mem_rlast),
		.M_AXI_RID(mem_rid),
		.M_AXI_RRESP(mem_rresp),
		// }}}
		// External interface
		// {{{
		// Bypass the external interface, connecting the output
		// back into the input (it'll be ignored anyway)
		.M_VID_ACLK(vid_aclk), .M_VID_ARESETN(vid_reset_n),
		//
		.M_VID_TVALID(vsrc_tvalid), .M_VID_TREADY(vsrc_tready),
		.M_VID_TDATA(vsrc_tdata),   .M_VID_TUSER(vsrc_tuser),
		.M_VID_TLAST(vsrc_tlast),

		.S_VID_TVALID(vsnk_tvalid), .S_VID_TREADY(vsnk_tready),
		.S_VID_TDATA(vsnk_tdata),   .S_VID_TUSER(vsnk_tuser),
		.S_VID_TLAST(vsnk_tlast),
		// }}}
		// Pixel output interface(s)
		// {{{
		.i_pixclk(i_pixclk),
		.o_clock_word(genclk_word),
`ifdef	HDMI
		// HDMI output words
		.o_hdmi_red(o_hdmi_red),
		.o_hdmi_grn(o_hdmi_grn),
		.o_hdmi_blu(o_hdmi_blu)
`else
		// Equivalent VGA output
		.o_vga_vsync(o_vga_vsync),
		.o_vga_hsync(o_vga_hsync),
		.o_vga_red(o_vga_red),
		.o_vga_grn(o_vga_grn),
		.o_vga_blu(o_vga_blu)
`endif
		// }}}
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The Sprite demo
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	axissprite #(
		// {{{
		.XSIZE(64), .YSIZE(64),
		.INITIAL_MEM(SPRITE_FILE),
		.OPT_TUSER_IS_SOF(1'b0)
		// }}}
	) u_sprite (
		// {{{
		.S_AXI_ACLK(i_clk),    .S_AXI_ARESETN(!i_reset),	// Systm
		.S_VID_ACLK(vid_aclk), .S_VID_ARESETN(vid_reset_n),
		// Control interface
		// {{{
		.S_AXI_AWVALID(axil_sprite_awvalid),
		.S_AXI_AWREADY(axil_sprite_awready),
		.S_AXI_AWADDR( axil_sprite_awaddr[14:0]),
		.S_AXI_AWPROT( axil_sprite_awprot),
		//
		.S_AXI_WVALID(axil_sprite_wvalid),
		.S_AXI_WREADY(axil_sprite_wready),
		.S_AXI_WDATA( axil_sprite_wdata),
		.S_AXI_WSTRB( axil_sprite_wstrb),
		//
		.S_AXI_BVALID(axil_sprite_bvalid),
		.S_AXI_BREADY(axil_sprite_bready),
		.S_AXI_BRESP( axil_sprite_bresp),
		//
		.S_AXI_ARVALID(axil_sprite_arvalid),
		.S_AXI_ARREADY(axil_sprite_arready),
		.S_AXI_ARADDR( axil_sprite_araddr[14:0]),
		.S_AXI_ARPROT( axil_sprite_arprot),
		//
		.S_AXI_RVALID(axil_sprite_rvalid),
		.S_AXI_RREADY(axil_sprite_rready),
		.S_AXI_RDATA( axil_sprite_rdata),
		.S_AXI_RRESP( axil_sprite_rresp),
		// }}}
		// Video interface
		// {{{
		// Incoming
		.S_AXIS_TVALID(vsrc_tvalid), .S_AXIS_TREADY(vsrc_tready),
		.S_AXIS_TDATA( vsrc_tdata),  .S_AXIS_TUSER( vsrc_tuser),
		.S_AXIS_TLAST( vsrc_tlast),
		// Outgoing / result
		.M_AXIS_TVALID(vsnk_tvalid), .M_AXIS_TREADY(vsnk_tready),
		.M_AXIS_TDATA( vsnk_tdata),  .M_AXIS_TUSER( vsnk_tuser),
		.M_AXIS_TLAST( vsnk_tlast)
		// }}}
		// }}}
	);

	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, mem_bvalid, mem_awready, mem_wready,
				mem_bid, mem_bresp, genclk_word,
			axil_sprite_awaddr[15], axil_sprite_araddr[15],
			axil_vid_awaddr[15:11], axil_vid_araddr[15:11]
			};
	// verilator lint_on  UNUSED
	// }}}
endmodule
