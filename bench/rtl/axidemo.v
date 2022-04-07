////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axidemo.v
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
// Copyright (C) 2020-2022, Gisselquist Technology, LLC
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
module	axidemo #(
		// {{{
		parameter AXI_ADDR_WIDTH = 26,
		parameter AXI_DATA_WIDTH = 32,
		parameter AXI_ID_WIDTH = 1,
		parameter AW = AXI_ADDR_WIDTH,
		parameter DW = AXI_DATA_WIDTH,
		parameter IW = AXI_ID_WIDTH,
		//
		parameter C_AXIL_ADDR_WIDTH = 11,
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
	// Internal AXI interface
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

	// RAM interface
	wire			ram_we, ram_rd;
	reg	[AWW-1:0]	ram_waddr, ram_raddr;
	reg	[DW-1:0]	ram_wdata, ram_rdata;
	reg	[DW/8-1:0]	ram_wstrb;
	reg	[DW-1:0]	ram	[0:(1<<AWW)-1];
	integer			rk;

	// (Unused) clock output generator
	wire	[7:0]	genclk_word;

	// (Unused) external video interface
	wire	ex_clk, ex_aresetn;
	wire	ex_tvalid, ex_tready;
	wire	[23:0]	ex_tdata;
	wire		ex_tuser, ex_tlast;
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
		.OPT_EXTERNAL(1'b0)
		// }}}
	) video (
		// {{{
		.S_AXI_ACLK(i_clk),
		.S_AXI_ARESETN(!i_reset),
		// AXI-lite control interface
		// {{{
		.S_AXIL_AWVALID(S_AXI_AWVALID),
		.S_AXIL_AWREADY(S_AXI_AWREADY),
		.S_AXIL_AWADDR(S_AXI_AWADDR),
		.S_AXIL_AWPROT(S_AXI_AWPROT),
		//
		.S_AXIL_WVALID(S_AXI_WVALID),
		.S_AXIL_WREADY(S_AXI_WREADY),
		.S_AXIL_WDATA( S_AXI_WDATA),
		.S_AXIL_WSTRB( S_AXI_WSTRB),
		//
		.S_AXIL_BVALID(S_AXI_BVALID),
		.S_AXIL_BREADY(S_AXI_BREADY),
		.S_AXIL_BRESP( S_AXI_BRESP),
		//
		.S_AXIL_ARVALID(S_AXI_ARVALID),
		.S_AXIL_ARREADY(S_AXI_ARREADY),
		.S_AXIL_ARADDR(S_AXI_ARADDR),
		.S_AXIL_ARPROT(S_AXI_ARPROT),
		//
		.S_AXIL_RVALID(S_AXI_RVALID),
		.S_AXIL_RREADY(S_AXI_RREADY),
		.S_AXIL_RDATA(S_AXI_RDATA),
		.S_AXIL_RRESP(S_AXI_RRESP),
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
		.M_VID_ACLK(ex_clk), .M_VID_ARESETN(ex_aresetn),
		//
		.M_VID_TVALID(ex_tvalid), .M_VID_TREADY(ex_tready),
		.M_VID_TDATA(ex_tdata),   .M_VID_TUSER(ex_tuser),
		.M_VID_TLAST(ex_tlast),

		.S_VID_TVALID(ex_tvalid), .S_VID_TREADY(ex_tready),
		.S_VID_TDATA(ex_tdata),   .S_VID_TUSER(ex_tuser),
		.S_VID_TLAST(ex_tlast),
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

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, mem_bvalid, mem_awready, mem_wready,
				mem_bid, mem_bresp, genclk_word,
				ex_clk, ex_aresetn
				};
	// verilator lint_on  UNUSED
	// }}}
endmodule
