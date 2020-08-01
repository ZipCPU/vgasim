////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmi2vga.v
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	Convert an HDMI input stream into an outgoing VGA stream,
//		for further processing as a (nearly video format independent)
//	stream.
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
module	hdmi2vga // #()	// No parameters (yet)
	(
		input	wire	i_clk,
		input	wire	[9:0]	i_hdmi_blu,
		input	wire	[9:0]	i_hdmi_grn,
		input	wire	[9:0]	i_hdmi_red,
		//
		output	reg		o_pix_valid,
		output	reg		o_vsync,
		output	reg		o_hsync,
		output	reg	[7:0]	o_vga_red, o_vga_green, o_vga_blue
	);

	wire	[1:0]	blu_ctl, grn_ctl, red_ctl;
	wire	[6:0]	blu_aux, grn_aux, red_aux;
	wire	[7:0]	blu_pix, grn_pix, red_pix;

	wire		video_guard, data_guard, control_sync;
	reg	[7:0]	video_preamble_sreg, data_preamble_sreg;
	reg	[1:0]	video_guard_sreg, data_guard_sreg;
	reg	[11:0]	control_sync_sreg;


	tmdsdecode
	decblu(i_clk, i_hdmi_blu, blu_ctl, blu_aux, blu_pix);

	tmdsdecode
	decgrn(i_clk, i_hdmi_grn, grn_ctl, grn_aux, grn_pix);

	tmdsdecode
	decred(i_clk, i_hdmi_red, red_ctl, red_aux, red_pix);

	// assign	blu_guard = blu_aux[5];
	// assign	grn_guard = grn_aux[5];
	// assign	red_guard = red_aux[5];

	reg	[7:0]	video_guard, data_guard;
	always @(posedge i_clk)
	begin
		// GUARD periods are 8-clocks long, and consist of only
		// control characters.

		// The specification says that the HSYNC & VSYNC signals can
		// do anything during the guard period.  Nominally, this would
		// affect the HDMI_BLUE channel.  However, there are no video
		// modes that would leave HSYNC or VSYNC active immeidately
		// prior to video, so we insist those two be inactive for
		// our purposes here.
		video_preamble_sreg[6:1] <=  video_preamble_sreg[5:0];
		video_preamble_sreg[7]   <= &video_preamble_sreg[6:0];
		video_preamble_sreg[0] <= (blu_aux[4])
			&&(grn_aux[4] && grn_ctl == 2'b10)
			&&(red_aux[4] && red_ctl == 2'b00);


		video_guard_sreg[1] <= video_guard_sreg[0];
		video_guard_sreg[0] <= (blu_aux[5] && !blu_aux[0])
				&&(grn_aux[6] &&  grn_aux[0])
				&&(red_aux[6] && !red_aux[0]);

		non_video_data <= (blu_aux[4])&&(grn_aux[4]) &&(red_aux[4]);

		data_preamble_sreg[6:1] <=  data_preamble_sreg[5:0];
		data_preamble_sreg[7]   <= &data_preamble_sreg[6:0];
		data_preamble_sreg[0] <= (blu_aux[4])
			&&(grn_aux[4] && grn_ctl == 2'b10)
			&&(red_aux[4] && red_ctl == 2'b10);

		data_guard_sreg[1] <= data_guard_sreg[0];
		data_guard_sreg[0] <=  (grn_aux[6] &&  grn_aux[0])
				&&(red_aux[6] && red_aux[0]);

		control_sync_sreg[10:1] <=  control_sync_sreg[ 9:0];
		control_sync_sreg[11]   <= &control_sync_sreg[10:0];
		control_sync_sreg <= blu_aux[5] && grn_aux[5] && red_aux[5];
	end

	assign	video_guard = video_preamble_sreg[ 7] && video_preamble_sreg[0]
				&& (&video_guard_sreg);
	assign	data_guard  = data_preamble_sreg[  7] && data_preamble_sreg[ 0]
				&& (&data_guard_sreg);
	assign	control_sync= control_sync_reg[11] && control_sync_sreg[0];

	always @(posedge i_clk)
	begin
		video_start <= video_preamble_sreg[7] && video_preamble_sreg[0]
				&& (&video_guard);
		data_start <= data_preamble_sreg[7] && data_preamble_sreg[0]
				&& (&data_guard);
		data_end <= data_period && (&data_guard);
		if (control_sync)
		begin
			data_period <= 0;
			video_period <= 0;
		end else begin
			if (video_start)
				video_period <= 1;
			else if (non_video_data)
				video_period <= 0;

			if (data_start)
				data_period <= 1;
			else if (data_end)
				data_period <= 0;
		end

		r_pix_valid <= (blu_aux[5:4] == 2'b00)
				&&(grn_aux[5:4] == 2'b00)
				&&(red_aux[5:4] == 2'b00);

		r_vga_red   <= red_pix;
		r_vga_green <= grn_pix;
		r_vga_blue  <= blu_pix;

		if (blu_aux[5:4] == 2'b01)
		begin
			o_vsync <= blu_ctl[1];
			o_hsync <= blu_ctl[0];
		end
	end

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, blu_aux[3:0], grn_aux[3:0], red_aux[3:0],
			grn_ctl, red_ctl };
	// Verilator lint_on  UNUSED
endmodule
