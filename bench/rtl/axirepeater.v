////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axirepeater.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Reads from an HDMI input and stores the result to memory.  Then
//		also reads from memory to generate an HDMI output.
//
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
`default_nettype	none
// }}}
module	axirepeater #(
		// {{{
		parameter	LGMEMSIZE = 28,
		localparam	C_AXIL_DATA_WIDTH = 32,
		localparam	C_AXIL_ADDR_WIDTH = 12,
		localparam	C_AXI_DATA_WIDTH  = 32,
		localparam	C_AXI_ADDR_WIDTH  = LGMEMSIZE,
		localparam	C_AXI_ID_WIDTH    = 1,
		//
		// Some abbreviations
		localparam	LAW = C_AXIL_ADDR_WIDTH,
		localparam	LDW = C_AXIL_DATA_WIDTH,
		localparam	AW = C_AXI_ADDR_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH,
		localparam	IW = C_AXI_ID_WIDTH
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		input	wire		i_reset,
		//
		// External AXI-lite control port
		input	wire		S_AXI_AWVALID,
		output	wire		S_AXI_AWREADY,
		input	wire [LAW-1:0]	S_AXI_AWADDR,
		input	wire [2:0]	S_AXI_AWPROT,
		//
		input	wire		S_AXI_WVALID,
		output	wire		S_AXI_WREADY,
		input	wire [LDW-1:0]	S_AXI_WDATA,
		input wire [LDW/8-1:0]	S_AXI_WSTRB,
		//
		output	wire		S_AXI_BVALID,
		input	wire		S_AXI_BREADY,
		output	wire	[1:0]	S_AXI_BRESP,
		//
		input	wire		S_AXI_ARVALID,
		output	wire		S_AXI_ARREADY,
		input	wire [LAW-1:0]	S_AXI_ARADDR,
		input	wire [2:0]	S_AXI_ARPROT,
		//
		output	wire		S_AXI_RVALID,
		input	wire		S_AXI_RREADY,
		output	wire [LDW-1:0]	S_AXI_RDATA,
		output	wire [1:0]	S_AXI_RRESP,
		//
		// Incoming HDMI stream
		input	wire		i_cam_clk,
		input	wire	[9:0]	i_cam_blu,
		input	wire	[9:0]	i_cam_grn,
		input	wire	[9:0]	i_cam_red,
		//
		// Outgoing HDMI stream
		input	wire		i_hdmi_clk,
		output	wire	[9:0]	o_hdmi_blu,
		output	wire	[9:0]	o_hdmi_grn,
		output	wire	[9:0]	o_hdmi_red
		// }}}
	);

	// Register/net declarations
	// {{{
	//
	// AXI-lite control wires for the incoming HDMI processor
	// {{{
	wire		axil_cam_awvalid;
	wire		axil_cam_awready;
	wire [LAW-1:0]	axil_cam_awaddr;
	wire [2:0]	axil_cam_awprot;
	//
	wire		axil_cam_wvalid;
	wire		axil_cam_wready;
	wire [LDW-1:0]	axil_cam_wdata;
	wire [LDW/8-1:0] axil_cam_wstrb;
	//
	wire		axil_cam_bvalid;
	wire		axil_cam_bready;
	wire	[1:0]	axil_cam_bresp;
	//
	wire		axil_cam_arvalid;
	wire		axil_cam_arready;
	wire [LAW-1:0]	axil_cam_araddr;
	wire [2:0]	axil_cam_arprot;
	//
	wire		axil_cam_rvalid;
	wire		axil_cam_rready;
	wire [LDW-1:0]	axil_cam_rdata;
	wire [1:0]	axil_cam_rresp;
	// }}}
	
	//
	// AXI-lite control wires for the outgoing HDMI processor
	// {{{
	wire		axil_hdmi_awvalid;
	wire		axil_hdmi_awready;
	wire [LAW-1:0]	axil_hdmi_awaddr;
	wire [2:0]	axil_hdmi_awprot;
	//
	wire		axil_hdmi_wvalid;
	wire		axil_hdmi_wready;
	wire [LDW-1:0]	axil_hdmi_wdata;
	wire [LDW/8-1:0] axil_hdmi_wstrb;
	//
	wire		axil_hdmi_bvalid;
	wire		axil_hdmi_bready;
	wire	[1:0]	axil_hdmi_bresp;
	//
	wire		axil_hdmi_arvalid;
	wire		axil_hdmi_arready;
	wire [LAW-1:0]	axil_hdmi_araddr;
	wire [2:0]	axil_hdmi_arprot;
	//
	wire		axil_hdmi_rvalid;
	wire		axil_hdmi_rready;
	wire [LDW-1:0]	axil_hdmi_rdata;
	wire [1:0]	axil_hdmi_rresp;
	// }}}


	//
	// AXI memory interface for the incoming HDMI processor
	// {{{
	wire		axi_cam_awvalid;
	wire		axi_cam_awready;
	wire [IW-1:0]	axi_cam_awid;
	wire [AW-1:0]	axi_cam_awaddr;
	wire [7:0]	axi_cam_awlen;
	wire [2:0]	axi_cam_awsize;
	wire [1:0]	axi_cam_awburst;
	wire 		axi_cam_awlock;
	wire [3:0]	axi_cam_awcache;
	wire [2:0]	axi_cam_awprot;
	wire [3:0]	axi_cam_awqos;
	//
	wire		axi_cam_wvalid;
	wire		axi_cam_wready;
	wire [DW-1:0]	axi_cam_wdata;
	wire [DW/8-1:0] axi_cam_wstrb;
	wire		axi_cam_wlast;
	//
	wire		axi_cam_bvalid;
	wire		axi_cam_bready;
	wire [IW-1:0]	axi_cam_bid;
	wire	[1:0]	axi_cam_bresp;
	//
	wire		axi_cam_arvalid;
	wire		axi_cam_arready;
	wire [IW-1:0]	axi_cam_arid;
	wire [AW-1:0]	axi_cam_araddr;
	wire [7:0]	axi_cam_arlen;
	wire [2:0]	axi_cam_arsize;
	wire [1:0]	axi_cam_arburst;
	wire 		axi_cam_arlock;
	wire [3:0]	axi_cam_arcache;
	wire [2:0]	axi_cam_arprot;
	wire [3:0]	axi_cam_arqos;
	//
	wire		axi_cam_rvalid;
	wire		axi_cam_rready;
	wire [IW-1:0]	axi_cam_rid;
	wire [DW-1:0]	axi_cam_rdata;
	wire		axi_cam_rlast;
	wire [1:0]	axi_cam_rresp;
	// }}}
	
	//
	// AXI memory interface for the outgoing HDMI display
	// {{{
	wire		axi_hdmi_awvalid;
	wire		axi_hdmi_awready;
	wire [IW-1:0]	axi_hdmi_awid;
	wire [AW-1:0]	axi_hdmi_awaddr;
	wire [7:0]	axi_hdmi_awlen;
	wire [2:0]	axi_hdmi_awsize;
	wire [1:0]	axi_hdmi_awburst;
	wire 		axi_hdmi_awlock;
	wire [3:0]	axi_hdmi_awcache;
	wire [2:0]	axi_hdmi_awprot;
	wire [3:0]	axi_hdmi_awqos;
	//
	wire		axi_hdmi_wvalid;
	wire		axi_hdmi_wready;
	wire [DW-1:0]	axi_hdmi_wdata;
	wire [DW/8-1:0] axi_hdmi_wstrb;
	wire		axi_hdmi_wlast;
	//
	wire		axi_hdmi_bvalid;
	wire		axi_hdmi_bready;
	wire [IW-1:0]	axi_hdmi_bid;
	wire	[1:0]	axi_hdmi_bresp;
	//
	wire		axi_hdmi_arvalid;
	wire		axi_hdmi_arready;
	wire [IW-1:0]	axi_hdmi_arid;
	wire [AW-1:0]	axi_hdmi_araddr;
	wire [7:0]	axi_hdmi_arlen;
	wire [2:0]	axi_hdmi_arsize;
	wire [1:0]	axi_hdmi_arburst;
	wire 		axi_hdmi_arlock;
	wire [3:0]	axi_hdmi_arcache;
	wire [2:0]	axi_hdmi_arprot;
	wire [3:0]	axi_hdmi_arqos;
	//
	wire		axi_hdmi_rvalid;
	wire		axi_hdmi_rready;
	wire [IW-1:0]	axi_hdmi_rid;
	wire [DW-1:0]	axi_hdmi_rdata;
	wire		axi_hdmi_rlast;
	wire [1:0]	axi_hdmi_rresp;

	// }}}

	// (Unused) external video interface
	wire	ex_clk, ex_aresetn;
	wire	ex_tvalid, ex_tready;
	wire	[23:0]	ex_tdata;
	wire		ex_tuser, ex_tlast;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite crossbar
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	axilxbar #(
		// {{{
		.C_AXI_DATA_WIDTH(LDW),
		.C_AXI_ADDR_WIDTH(LAW),
		.NM(1), .NS(2),
		.SLAVE_ADDR( {1'b0, {(LAW-1){1'b0}}, 1'b1, {(LAW-1){1'b0}} }),
		.SLAVE_MASK( {1'b1, {(LAW-1){1'b0}}, 1'b1, {(LAW-1){1'b0}} })
		// }}}
	) control_xbar (
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		// The slave interface, coming in from externally
		// {{{
		// where an incoming master may make a request
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
		// The outgoing connections: camera and display drivers
		// {{{
		.M_AXI_AWVALID({ axil_cam_awvalid, axil_hdmi_awvalid }),
		.M_AXI_AWREADY({ axil_cam_awready, axil_hdmi_awready }),
		.M_AXI_AWADDR( { axil_cam_awaddr,  axil_hdmi_awaddr }),
		.M_AXI_AWPROT( { axil_cam_awprot,  axil_hdmi_awprot }),
		//
		.M_AXI_WVALID({ axil_cam_wvalid, axil_hdmi_wvalid }),
		.M_AXI_WREADY({ axil_cam_wready, axil_hdmi_wready }),
		.M_AXI_WDATA( { axil_cam_wdata,  axil_hdmi_wdata }),
		.M_AXI_WSTRB( { axil_cam_wstrb,  axil_hdmi_wstrb }),
		//
		.M_AXI_BVALID({ axil_cam_bvalid, axil_hdmi_bvalid }),
		.M_AXI_BREADY({ axil_cam_bready, axil_hdmi_bready }),
		.M_AXI_BRESP( { axil_cam_bresp,  axil_hdmi_bresp }),
		//
		.M_AXI_ARVALID({ axil_cam_arvalid, axil_hdmi_arvalid }),
		.M_AXI_ARREADY({ axil_cam_arready, axil_hdmi_arready }),
		.M_AXI_ARADDR( { axil_cam_araddr,  axil_hdmi_araddr }),
		.M_AXI_ARPROT( { axil_cam_arprot,  axil_hdmi_arprot }),
		//
		.M_AXI_RVALID({ axil_cam_rvalid, axil_hdmi_rvalid }),
		.M_AXI_RREADY({ axil_cam_rready, axil_hdmi_rready }),
		.M_AXI_RDATA( { axil_cam_rdata,  axil_hdmi_rdata }),
		.M_AXI_RRESP( { axil_cam_rresp,  axil_hdmi_rresp })
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	localparam		AWW = AW-$clog2(DW/8);
	wire			ram_we, ram_rd;
	wire	[AWW-1:0]	ram_waddr, ram_raddr;
	wire	[DW-1:0]	ram_wdata;
	wire	[DW/8-1:0]	ram_wstrb;
	reg	[DW-1:0]	ram_rdata;
	reg	[DW-1:0]	ram	[0:(1<<AWW)-1];
	integer			rk;

	//
	// First, the protocol processor
	//
	demofull #(
		// {{{
		.C_S_AXI_ID_WIDTH(IW),
		.C_S_AXI_DATA_WIDTH(DW),
		.C_S_AXI_ADDR_WIDTH(AW)
		// }}}
	) aximemory (
		// {{{
		.S_AXI_ACLK(i_clk),
		.S_AXI_ARESETN(!i_reset),
		// AXI memory (slave) interface
		// {{{
		.S_AXI_AWVALID(axi_cam_awvalid),
		.S_AXI_AWREADY(axi_cam_awready),
		.S_AXI_AWID(   axi_cam_awid),
		.S_AXI_AWADDR( axi_cam_awaddr),
		.S_AXI_AWLEN(  axi_cam_awlen),
		.S_AXI_AWSIZE( axi_cam_awsize),
		.S_AXI_AWBURST(axi_cam_awburst),
		.S_AXI_AWLOCK( axi_cam_awlock),
		.S_AXI_AWCACHE(axi_cam_awcache),
		.S_AXI_AWPROT( axi_cam_awprot),
		.S_AXI_AWQOS(  axi_cam_awqos),
		//
		.S_AXI_WVALID(axi_cam_wvalid),
		.S_AXI_WREADY(axi_cam_wready),
		.S_AXI_WDATA( axi_cam_wdata),
		.S_AXI_WSTRB( axi_cam_wstrb),
		.S_AXI_WLAST( axi_cam_wlast),
		//
		.S_AXI_BVALID(axi_cam_bvalid),
		.S_AXI_BREADY(axi_cam_bready),
		.S_AXI_BID(   axi_cam_bid),
		.S_AXI_BRESP( axi_cam_bresp),
		//
		.S_AXI_ARVALID(axi_hdmi_arvalid),
		.S_AXI_ARREADY(axi_hdmi_arready),
		.S_AXI_ARID(   axi_hdmi_arid),
		.S_AXI_ARADDR( axi_hdmi_araddr),
		.S_AXI_ARLEN(  axi_hdmi_arlen),
		.S_AXI_ARSIZE( axi_hdmi_arsize),
		.S_AXI_ARBURST(axi_hdmi_arburst),
		.S_AXI_ARLOCK( axi_hdmi_arlock),
		.S_AXI_ARCACHE(axi_hdmi_arcache),
		.S_AXI_ARPROT( axi_hdmi_arprot),
		.S_AXI_ARQOS(  axi_hdmi_arqos),
		//
		.S_AXI_RVALID(axi_hdmi_rvalid),
		.S_AXI_RREADY(axi_hdmi_rready),
		.S_AXI_RID(   axi_hdmi_rid),
		.S_AXI_RDATA( axi_hdmi_rdata),
		.S_AXI_RLAST( axi_hdmi_rlast),
		.S_AXI_RRESP( axi_hdmi_rresp),
		// }}}
		// A raw memory interface to an external memory
		// {{{
		.o_we(ram_we),
		.o_waddr(ram_waddr),
		.o_wdata(ram_wdata),
		.o_wstrb(ram_wstrb),
		.o_rd(ram_rd),
		.o_raddr(ram_raddr),
		.i_rdata(ram_rdata)
		// }}}
		// }}}
	);

	//
	// The raw memory implementation itself
	// {{{
	always @(posedge i_clk)
	for(rk=0; rk<DW/8; rk=rk+1)
	if (ram_we && ram_wstrb[rk])
		ram[ram_waddr][rk*8 +: 8] <= ram_wdata[rk*8 +: 8];

	always @(posedge i_clk)
	if (ram_rd)
		ram_rdata <= ram[ram_raddr];
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// HDMI input (camera) processing
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire		cam_pix_valid, cam_vsync, cam_hsync;
	wire [23:0]	cam_pixel;

	// Convert HDMI to a digitized (VGA) pixel stream
	// {{{
	hdmi2vga
	topixels(
		.i_clk(i_cam_clk),
		.i_reset(i_reset),
		.i_hdmi_blu(i_cam_blu), .i_hdmi_grn(i_cam_grn),
			.i_hdmi_red(i_cam_red),
		.o_pix_valid(cam_pix_valid),
			.o_vsync(cam_vsync), .o_hsync(cam_hsync),
		.o_vga_red(cam_pixel[23:16]),
			.o_vga_green(cam_pixel[15:8]),
			.o_vga_blue(cam_pixel[7:0])
	);
	// }}}

	axicamera #(
		// {{{
		.C_AXI_ADDR_WIDTH(AW),
		.C_AXI_DATA_WIDTH(DW),
		.C_AXI_ID_WIDTH(IW)
		// }}}
	) camdma (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		// Video pixel port
		// {{{
		.i_pix_clk(i_cam_clk),
		.i_pix_valid(cam_pix_valid),
		.i_pixel(cam_pixel),
		.i_hsync(cam_hsync),
		.i_vsync(cam_vsync),
		// }}}
		// AXI-lite control
		// {{{
		.S_AXIL_AWVALID(axil_cam_awvalid),
		.S_AXIL_AWREADY(axil_cam_awready),
		.S_AXIL_AWADDR( axil_cam_awaddr[5:0]),
		.S_AXIL_AWPROT( axil_cam_awprot),
		//
		.S_AXIL_WVALID(axil_cam_wvalid),
		.S_AXIL_WREADY(axil_cam_wready),
		.S_AXIL_WDATA( axil_cam_wdata),
		.S_AXIL_WSTRB( axil_cam_wstrb),
		//
		.S_AXIL_BVALID(axil_cam_bvalid),
		.S_AXIL_BREADY(axil_cam_bready),
		.S_AXIL_BRESP( axil_cam_bresp),
		//
		.S_AXIL_ARVALID(axil_cam_arvalid),
		.S_AXIL_ARREADY(axil_cam_arready),
		.S_AXIL_ARADDR( axil_cam_araddr[5:0]),
		.S_AXIL_ARPROT( axil_cam_arprot),
		//
		.S_AXIL_RVALID(axil_cam_rvalid),
		.S_AXIL_RREADY(axil_cam_rready),
		.S_AXIL_RDATA( axil_cam_rdata),
		.S_AXIL_RRESP( axil_cam_rresp),
		// }}}
		// AXI (full) master memory write interface
		// {{{
		.M_AXI_AWVALID(axi_cam_awvalid),
		.M_AXI_AWREADY(axi_cam_awready),
		.M_AXI_AWID(   axi_cam_awid),
		.M_AXI_AWADDR( axi_cam_awaddr),
		.M_AXI_AWLEN(  axi_cam_awlen),
		.M_AXI_AWSIZE( axi_cam_awsize),
		.M_AXI_AWBURST(axi_cam_awburst),
		.M_AXI_AWLOCK( axi_cam_awlock),
		.M_AXI_AWCACHE(axi_cam_awcache),
		.M_AXI_AWPROT( axi_cam_awprot),
		.M_AXI_AWQOS(  axi_cam_awqos),
		//
		.M_AXI_WVALID(axi_cam_wvalid),
		.M_AXI_WREADY(axi_cam_wready),
		.M_AXI_WDATA( axi_cam_wdata),
		.M_AXI_WSTRB( axi_cam_wstrb),
		.M_AXI_WLAST( axi_cam_wlast),
		//
		.M_AXI_BVALID(axi_cam_bvalid),
		.M_AXI_BREADY(axi_cam_bready),
		.M_AXI_BID(   axi_cam_bid),
		.M_AXI_BRESP( axi_cam_bresp),
		//
		.M_AXI_ARVALID(axi_cam_arvalid),
		.M_AXI_ARREADY(axi_cam_arready),
		.M_AXI_ARID(   axi_cam_arid),
		.M_AXI_ARADDR( axi_cam_araddr),
		.M_AXI_ARLEN(  axi_cam_arlen),
		.M_AXI_ARSIZE( axi_cam_arsize),
		.M_AXI_ARBURST(axi_cam_arburst),
		.M_AXI_ARLOCK( axi_cam_arlock),
		.M_AXI_ARCACHE(axi_cam_arcache),
		.M_AXI_ARPROT( axi_cam_arprot),
		.M_AXI_ARQOS(  axi_cam_arqos),
		//
		.M_AXI_RVALID(axi_cam_rvalid),
		.M_AXI_RREADY(axi_cam_rready),
		.M_AXI_RID(   axi_cam_rid),
		.M_AXI_RDATA( axi_cam_rdata),
		.M_AXI_RLAST( axi_cam_rlast),
		.M_AXI_RRESP( axi_cam_rresp)
		// }}}
		// }}}
	);

	// Fill out the unused memory read interface
	assign	axi_cam_arready = 0;
	assign	axi_cam_rvalid  = 0;
	assign	axi_cam_rid     = 0;
	assign	axi_cam_rdata   = 0;
	assign	axi_cam_rlast   = 0;
	assign	axi_cam_rresp   = 0;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// HDMI output (display) processing
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire	[7:0]	unused_clk_word;

	axivideo #(
		// {{{
		.C_AXI_ADDR_WIDTH(AW),
		.C_AXI_DATA_WIDTH(DW),
		.C_AXI_ID_WIDTH(IW)
		// }}}
	) video (
		// {{{
		.S_AXI_ACLK(i_clk),
		.S_AXI_ARESETN(!i_reset),
		// AXI-lite control port
		// {{{
		.S_AXIL_AWVALID(axil_hdmi_awvalid),
		.S_AXIL_AWREADY(axil_hdmi_awready),
		.S_AXIL_AWADDR( axil_hdmi_awaddr[10:0]),
		.S_AXIL_AWPROT( axil_hdmi_awprot),
		//
		.S_AXIL_WVALID(axil_hdmi_wvalid),
		.S_AXIL_WREADY(axil_hdmi_wready),
		.S_AXIL_WDATA( axil_hdmi_wdata),
		.S_AXIL_WSTRB( axil_hdmi_wstrb),
		//
		.S_AXIL_BVALID(axil_hdmi_bvalid),
		.S_AXIL_BREADY(axil_hdmi_bready),
		.S_AXIL_BRESP( axil_hdmi_bresp),
		//
		.S_AXIL_ARVALID(axil_hdmi_arvalid),
		.S_AXIL_ARREADY(axil_hdmi_arready),
		.S_AXIL_ARADDR( axil_hdmi_araddr[10:0]),
		.S_AXIL_ARPROT( axil_hdmi_arprot),
		//
		.S_AXIL_RVALID(axil_hdmi_rvalid),
		.S_AXIL_RREADY(axil_hdmi_rready),
		.S_AXIL_RDATA( axil_hdmi_rdata),
		.S_AXIL_RRESP( axil_hdmi_rresp),
		// }}}
		// AXI (full) master memory read port
		// {{{
		.M_AXI_ARVALID(axi_hdmi_arvalid),
		.M_AXI_ARREADY(axi_hdmi_arready),
		.M_AXI_ARID(   axi_hdmi_arid),
		.M_AXI_ARADDR( axi_hdmi_araddr),
		.M_AXI_ARLEN(  axi_hdmi_arlen),
		.M_AXI_ARSIZE( axi_hdmi_arsize),
		.M_AXI_ARBURST(axi_hdmi_arburst),
		.M_AXI_ARLOCK( axi_hdmi_arlock),
		.M_AXI_ARCACHE(axi_hdmi_arcache),
		.M_AXI_ARPROT( axi_hdmi_arprot),
		.M_AXI_ARQOS(  axi_hdmi_arqos),
		//
		.M_AXI_RVALID(axi_hdmi_rvalid),
		.M_AXI_RREADY(axi_hdmi_rready),
		.M_AXI_RID(   axi_hdmi_rid),
		.M_AXI_RDATA( axi_hdmi_rdata),
		.M_AXI_RLAST( axi_hdmi_rlast),
		.M_AXI_RRESP( axi_hdmi_rresp),
		// }}}
		// External interface
		// {{{
		// Bypass the external interface, connecting the output
		// back into the input (it'll be ignored anyway)
		.M_VID_ACLK(ex_clk), .M_VID_ARESETN(ex_aresetn),
		//
		.M_VID_TVALID(ex_tvalid), .M_VID_TREADY(ex_tready),
		.M_VID_TDATA(ex_tdata),   .M_VID_TUSER(ex_tuser),
		.M_VID_TLAST(ex_tlast),

		.S_VID_TVALID(ex_tvalid), .S_VID_TREADY(ex_tready),
		.S_VID_TDATA(ex_tdata),   .S_VID_TUSER(ex_tuser),
		.S_VID_TLAST(ex_tlast),
		// }}}
		// HDMI output video stream
		// {{{
		.i_pixclk(    i_hdmi_clk),
		.o_clock_word(unused_clk_word),
		.o_hdmi_red(  o_hdmi_red),
		.o_hdmi_grn(  o_hdmi_grn),
		.o_hdmi_blu(  o_hdmi_blu)
		// }}}
		// }}}
	);
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0,
		// {{{
		axi_hdmi_awvalid, axi_hdmi_awready, axi_hdmi_awid,
		axi_hdmi_awaddr, axi_hdmi_awlen, axi_hdmi_awsize,
		axi_hdmi_awburst, axi_hdmi_awlock, axi_hdmi_awcache,
		axi_hdmi_awprot, axi_hdmi_awqos, axi_hdmi_wvalid,
		axi_hdmi_wready, axi_hdmi_wdata, axi_hdmi_wstrb,
		axi_hdmi_wlast,
		axi_hdmi_bvalid, axi_hdmi_bready, axi_hdmi_bid,
		axi_hdmi_bresp,
		//
		axi_cam_arvalid, axi_cam_arready, axi_cam_arid, axi_cam_araddr,
		axi_cam_arlen, axi_cam_arsize, axi_cam_arburst, axi_cam_arlock,
		axi_cam_arcache, axi_cam_arprot, axi_cam_arqos,
		//
		axi_cam_rready,
		//
		axil_cam_awaddr[11:6], axil_cam_araddr[11:6],
		axil_hdmi_awaddr[11],  axil_hdmi_araddr[11],
		//
		ex_clk, ex_aresetn,
		//
		1'b0
		// }}}
		};
	// Verilator lint_on  UNUSED

	assign	axi_hdmi_awvalid = 0;
	assign	axi_hdmi_awready = 0;
	assign	axi_hdmi_awid    = 0;
	assign	axi_hdmi_awaddr  = 0;
	assign	axi_hdmi_awlen   = 0;
	assign	axi_hdmi_awsize  = 0;
	assign	axi_hdmi_awburst = 0;
	assign	axi_hdmi_awlock  = 0;
	assign	axi_hdmi_awcache = 0;
	assign	axi_hdmi_awprot  = 0;
	assign	axi_hdmi_awqos   = 0;
	assign	axi_hdmi_wvalid  = 0;
	assign	axi_hdmi_wready  = 0;
	assign	axi_hdmi_wdata   = 0;
	assign	axi_hdmi_wstrb   = 0;
	assign	axi_hdmi_wlast   = 0;
	assign	axi_hdmi_bvalid  = 0;
	assign	axi_hdmi_bready  = 0;
	assign	axi_hdmi_bid     = 0;
	assign	axi_hdmi_bresp   = 0;
/*
		.M_AXI_RVALID(axi_hdmi_rvalid),
		.M_AXI_RID(   axi_hdmi_rid),
		.M_AXI_RDATA( axi_hdmi_rdata),
		.M_AXI_RLAST( axi_hdmi_rlast),
		.M_AXI_RRESP( axi_hdmi_rresp),
		//
		.i_pixclk(    i_hdmi_clk),
*/
	// }}}
endmodule
