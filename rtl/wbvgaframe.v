////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbvgaframe.v
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017, Gisselquist Technology, LLC
//
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
//
module	wbvgaframe(i_clk, i_pixclk,
		// Command and control
		i_reset, i_en, i_test,
		//
		i_base_addr, i_line_addr,
		i_hm_width, i_hm_porch, i_hm_synch, i_hm_raw,
		i_vm_height, i_vm_porch, i_vm_synch, i_vm_raw,
		// Wishbone interface
		o_wb_cyc, o_wb_stb, o_wb_addr,
			i_wb_ack, i_wb_stall, i_wb_data,
		// VGA output
		o_vga_vsync, o_vga_hsync, o_vga_red, o_vga_grn, o_vga_blu,
		// Offer frame interrupts to ... whoever's interested.
		o_interrupt);
	parameter	ADDRESS_WIDTH=24,
			BUS_DATA_WIDTH=64;
	localparam	AW=ADDRESS_WIDTH;
	parameter	BITS_PER_COLOR = 8;
	localparam	BPC = BITS_PER_COLOR,
			DW=BUS_DATA_WIDTH;
	input	wire		i_clk, i_pixclk, i_reset;
	input	wire		i_en, i_test;
	//
	input	wire	[(AW-1):0]	i_base_addr;
	input	wire	[(AW-1):0]	i_line_addr;
	//
	input	wire	[11:0]	i_hm_width, i_hm_porch, i_hm_synch, i_hm_raw;
	input	wire	[11:0]	i_vm_height, i_vm_porch, i_vm_synch, i_vm_raw;
	//
	output	wire			o_wb_cyc, o_wb_stb;
	output	wire	[(AW-1):0]	o_wb_addr;
	input	wire			i_wb_ack, i_wb_stall;
	input	wire	[(DW-1):0]	i_wb_data;
	//
	output	wire		o_vga_vsync, o_vga_hsync;
	output	wire [BPC-1:0]	o_vga_red, o_vga_grn, o_vga_blu;
	//
	output	wire		o_interrupt;

	wire	vga_newline, vga_newframe, vga_rd;

`ifdef	INITIAL
	imgfifo #(AW, DW, 32)
		readmem(i_clk, i_pixclk,
			(i_reset)||(i_en)||(i_test),(o_vga_newframe),
				i_base_addr, i_line_addr, i_vm_height,
				o_wb_cyc, o_wb_stb, o_wb_addr,
					i_wb_ack, i_wb_stall, i_wb_data,
				vga_rd, fifo_err);
`else
	wire	[(3*BPC-1):0]	pixel;
	assign	pixel = 0;

	assign	o_wb_cyc = 1'b0;
	assign	o_wb_stb = 1'b0;
	assign	o_wb_addr = 0;

	wire	[(2+(DW+2)+(2*AW)+2-1):0]	wb_unused;
	assign	wb_unused = { i_clk, i_en,
			i_wb_ack, i_wb_stall, i_wb_data,
			i_base_addr, i_line_addr,
			vga_rd, vga_newline };
`endif

	// Actually control the VGA hardware, produce the sync's, and output
	// the color data given
	llvga	#(BPC)	vgahw(i_pixclk, (i_reset), i_test,
				pixel[(3*BPC-1):0],
				i_hm_width, i_hm_porch, i_hm_synch, i_hm_raw,
				i_vm_height, i_vm_porch, i_vm_synch, i_vm_raw,
				vga_rd, vga_newline, vga_newframe,
				o_vga_vsync, o_vga_hsync,
				o_vga_red, o_vga_grn, o_vga_blu);

	assign	o_interrupt = vga_newframe;

	// Make verilator happy
	// verilator lint_off UNUSED
	// wire	[33:0] unused;
	// assign	unused = { read_err, imdec_err, pal_val };
	// verilator lint_on  UNUSED
endmodule
