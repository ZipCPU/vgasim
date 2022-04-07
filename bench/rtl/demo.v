////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	demo.v
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
// Copyright (C) 2018-2022, Gisselquist Technology, LLC
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
module	demo(i_clk, i_pixclk, i_reset, i_test,
		//
		i_hm_width, i_hm_porch, i_hm_synch, i_hm_raw,
		i_vm_height,i_vm_porch, i_vm_synch, i_vm_raw,
		//
		o_vga_vsync, o_vga_hsync, o_vga_red, o_vga_grn, o_vga_blu,
		o_interrupt);
	parameter	BW=32,
			FW=13,	// Log_2 of the maximum width or FIFO size
			LW=11;	// Log_2 of the number of lines
	localparam	AW=(FW+LW);
	input	wire		i_clk, i_pixclk, i_reset;
	input	wire		i_test;
	//
	input	wire	[FW-1:0] i_hm_width, i_hm_porch, i_hm_synch, i_hm_raw;
	input	wire	[LW-1:0] i_vm_height,i_vm_porch, i_vm_synch, i_vm_raw;
	//
	output	wire		o_vga_vsync, o_vga_hsync;
	output	wire	[7:0]	o_vga_red, o_vga_grn, o_vga_blu;
	output	wire		o_interrupt;

	wire			wb_cyc, wb_stb;
	wire	[AW-1:0]	wb_addr;
	//
	wire			mem_ack, mem_stall;
	wire	[31:0]		mem_data;

	memdev	#(.LGMEMSZ(AW+2),.DW(BW), .HEXFILE("slide.hex"), .OPT_ROM(1'b1))
		memi(i_clk, i_reset,
			wb_cyc, wb_stb, 1'b0, wb_addr, 32'h0, 4'h0,
			mem_ack, mem_stall, mem_data);

	wbvgaframe	#(.ADDRESS_WIDTH(AW), .BUS_DATA_WIDTH(BW),
			.FW(FW), .LW(LW))
		vgai(i_clk, i_pixclk, i_reset, 1'b1, i_test,
			0, { 1'b0, i_hm_width },
			i_hm_width, i_hm_porch, i_hm_synch, i_hm_raw,
			i_vm_height,i_vm_porch, i_vm_synch, i_vm_raw,
			//
			wb_cyc, wb_stb, wb_addr,
				mem_ack, 1'b0, 1'b0, mem_data,
			o_vga_vsync, o_vga_hsync,
				o_vga_red, o_vga_grn, o_vga_blu,
			o_interrupt);


	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = mem_stall;
	// verilator lint_on  UNUSED
endmodule
