////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilcam.v
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	
// Registers:
//	000:	(DMA) Control, color mapping, lock status
//
//	004:	DMA line words		(Must match to stay in sync)
//	006:	DMA Number of lines	(Must match to stay in sync)
//	008:	Frame base address	(May not wrap across memory)
//	00c:	(Frame base address, upper word)
//	010:	Pixel clock status
//	014:	(Reserved)
//	018:	(Reserved)
//	01c:	(Reserved)
//	020:	Horizontal image size (pixel width)
//	022:	Vertical image size (pixel height)
//	024:	Distances from pixels to sync
//	028:	Sync duration
//	02c:	Raw image size (clocks/width, rows / frame)
//	030+:	(Reserved, may be mapped onto otherr addresses)
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018, Gisselquist Technology, LLC
//
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
//
module	axicam #(
		localparam	C_AXIL_ADDR_WIDTH = 6,
		localparam	C_AXIL_DATA_WIDTH = 32,
		parameter	C_AXI_ADDR_WIDTH = 40,
		parameter	C_AXI_DATA_WIDTH = 64,
		parameter	CLOCK_FREQUENCY = 100_000_000,
		parameter	LGFIFO = 10,
		parameter	LGAFIFO= 5,
	) (
	input	wire	S_AXI_ACLK,
	input	wire	S_AXI_ARESETN,
	//
	// The video input port
	input	wire				i_pix_clk,
	input	wire 				i_pix_valid,
	input	wire [23:0]			i_pixel,
	input	wire				i_hsync,
	input	wire				i_vsync,
	//
	// The AXI-Lite control port
	input	wire				S_AXIL_AWVALID,
	output	wire				S_AXIL_AWREADY,
	input	wire [C_AXIL_ADDR_WIDTH-1:0]	S_AXIL_AWADDR,
	input	wire	[2:0]			S_AXIL_AWPROT,
	//
	input	wire				S_AXIL_WVALID,
	output	wire				S_AXIL_WREADY,
	input	wire [C_AXIL_DATA_WIDTH-1:0]	S_AXIL_WDATA,
	input	wire [C_AXIL_DATA_WIDTH/8-1:0]	S_AXIL_WSTRB,
	//
	output	reg				S_AXIL_BVALID,
	input	wire				S_AXIL_BREADY,
	output	reg	[1:0]			S_AXIL_BRESP,
	//
	input	wire				S_AXIL_ARVALID,
	output	wire				S_AXIL_ARREADY,
	input	wire [C_AXIL_ADDR_WIDTH-1:0]	S_AXIL_ARADDR,
	input	wire	[2:0]			S_AXIL_ARPROT,
	//
	output	reg				S_AXIL_RVALID,
	input	wire				S_AXIL_RREADY,
	output	reg [C_AXIL_DATA_WIDTH-1:0]	S_AXIL_RDATA,
	output	reg	[1:0]			S_AXIL_RRESP,
	//
	// The AXI Master DMA (write) port
	output	wire				M_AXI_AWVALID,
	input	wire				M_AXI_AWREADY,
	output	wire [C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
	output	wire [C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
	output	wire	[7:0]			M_AXI_AWLEN,
	output	wire	[2:0]			M_AXI_AWSIZE,
	output	wire	[1:0]			M_AXI_AWBURST,
	output	wire				M_AXI_AWLOCK,
	output	wire	[3:0]			M_AXI_AWCACHE,
	output	wire	[2:0]			M_AXI_AWPROT,
	output	wire	[3:0]			M_AXI_AWQOS,
	//
	output	wire				M_AXI_WVALID,
	input	wire				M_AXI_WREADY,
	output	wire [C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
	output	wire [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
	output	wire 				M_AXI_WLAST,
	//
	//
	input	wire				M_AXI_BVALID,
	output	wire				M_AXI_BREADY,
	output	wire [C_AXI_ID_WIDTH-1:0]	M_AXI_BID,
	output	wire	[1:0]			M_AXI_BRESP,
	);

	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite Control
	//
	////////////////////////////////////////////////////////////////////////
	//
	//


	////////////////////////////////////////////////////////////////////////
	//
	//  Video (pixel) processing
	////////////////////////////////////////////////////////////////////////
	//
	//
	sync2stream
	s2si(
		.i_clk(i_pix_clk), .i_reset(video_reset),
		.i_pix_valid(i_pix_valid), .i_hsync(i_hsync), .i_vsync(i_vsync),
		.i_pixel(i_pixel),
		//
		.M_AXIS_TVALID(pix_valid), .M_AXIS_TREADY(1'b1),
		.M_AXIS_TDATA(pix_data), .M_AXIS_TLAST(pix_vlast),
		.M_AXIS_TUSER(pix_hlast),
		//
		.o_width(pix_imwidth), .o_hfront(pix_imhfront),
		.o_hsync(pix_imhsync), .o_raw_width(pix_imwidth_raw),
		//
		.o_height(pix_imheight), .o_vfront(pix_imvfront),
		.o_vsync(pix_imvsync), .o_raw_height(pix_imheight_raw),
		//
		.o_locked(pix_locked)
	);

	always @(posedge S_AXI_ACLK)
		{ bus_imwidth, bus_imhfront, bus_imhsync, bus_imwidth_raw,
		  bus_imheight,bus_imvfront, bus_imvsync, bus_imheight_raw }
		<=
		{ pix_imwidth, pix_imhfront, pix_imhsync, pix_imwidth_raw,
		  pix_imheight,pix_imvfront, pix_imvsync, pix_imheight_raw };
sync2stream.v

	afifo #(
	) pixfifo (
		.i_wclk(i_pix_clk), .i_wr_reset_n(video_reset),
		.i_wr(pixw_valid),
		.i_wr_data({ pixw_vlast, pixw_hlast, pixw_data }),
		.o_wr_full(ign_fifo_full),
		//
		.i_rclk(S_AXI_ACLK), .i_rd_reset_n(!S_AXI_ARESETN),
		.i_rd(pixb_valid && pixb_ready),
		.o_rd_data({ pixb_vlast, pixb_hlast, pixb_data }),
		.o_rd_empty(pixb_empty)
	);

	assign	pixb_valid = !pixb_empty

	axivcamera #(
	) axidma (
	);
endmodule
