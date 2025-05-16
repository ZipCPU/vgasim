////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/gfx/vid_clrmap.v
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	This is my favorite false color map, one that I built years
//		ago and have used ever since for various projects.  A very
//	handy colormap as well.  Weak colors show up as black, strong colors
//	as white, and the shades in between go from blue to red, to orange,
//	to white.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2021-2025, Gisselquist Technology, LLC
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module	vid_clrmap (
		// {{{
		input	wire	[7:0]	i_pixel,
		output	reg	[7:0]	o_r, o_g, o_b
		// }}}
	);

	// Local declarations
	// {{{
	reg	[7:0]	rtbl	[0:255];
	reg	[7:0]	gtbl	[0:255];
	reg	[7:0]	btbl	[0:255];
	// }}}

	always @(*)
	begin
		o_r = rtbl[i_pixel];
		o_g = gtbl[i_pixel];
		o_b = btbl[i_pixel];
	end
	////////////////////////////////////////////////////////////////////////
	//
	// Now define the color table(s) themselves
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial begin
	rtbl[  0] = 8'h00; gtbl[  0] = 8'h00; btbl[  0] = 8'h00;
	rtbl[  1] = 8'h00; gtbl[  1] = 8'h00; btbl[  1] = 8'h00;
	rtbl[  2] = 8'h00; gtbl[  2] = 8'h00; btbl[  2] = 8'h00;
	rtbl[  3] = 8'h00; gtbl[  3] = 8'h00; btbl[  3] = 8'h01;
	rtbl[  4] = 8'h00; gtbl[  4] = 8'h00; btbl[  4] = 8'h02;
	rtbl[  5] = 8'h00; gtbl[  5] = 8'h00; btbl[  5] = 8'h03;
	rtbl[  6] = 8'h00; gtbl[  6] = 8'h00; btbl[  6] = 8'h05;
	rtbl[  7] = 8'h01; gtbl[  7] = 8'h00; btbl[  7] = 8'h07;
	rtbl[  8] = 8'h01; gtbl[  8] = 8'h00; btbl[  8] = 8'h09;
	rtbl[  9] = 8'h01; gtbl[  9] = 8'h00; btbl[  9] = 8'h0c;
	rtbl[ 10] = 8'h02; gtbl[ 10] = 8'h00; btbl[ 10] = 8'h0f;
	rtbl[ 11] = 8'h02; gtbl[ 11] = 8'h00; btbl[ 11] = 8'h12;
	rtbl[ 12] = 8'h03; gtbl[ 12] = 8'h00; btbl[ 12] = 8'h15;
	rtbl[ 13] = 8'h03; gtbl[ 13] = 8'h00; btbl[ 13] = 8'h19;
	rtbl[ 14] = 8'h04; gtbl[ 14] = 8'h00; btbl[ 14] = 8'h1d;
	rtbl[ 15] = 8'h04; gtbl[ 15] = 8'h00; btbl[ 15] = 8'h21;
	rtbl[ 16] = 8'h05; gtbl[ 16] = 8'h00; btbl[ 16] = 8'h25;
	rtbl[ 17] = 8'h06; gtbl[ 17] = 8'h00; btbl[ 17] = 8'h2a;
	rtbl[ 18] = 8'h06; gtbl[ 18] = 8'h00; btbl[ 18] = 8'h2e;
	rtbl[ 19] = 8'h07; gtbl[ 19] = 8'h00; btbl[ 19] = 8'h33;
	rtbl[ 20] = 8'h08; gtbl[ 20] = 8'h00; btbl[ 20] = 8'h38;
	rtbl[ 21] = 8'h09; gtbl[ 21] = 8'h00; btbl[ 21] = 8'h3e;
	rtbl[ 22] = 8'h0a; gtbl[ 22] = 8'h00; btbl[ 22] = 8'h43;
	rtbl[ 23] = 8'h0b; gtbl[ 23] = 8'h00; btbl[ 23] = 8'h49;
	rtbl[ 24] = 8'h0c; gtbl[ 24] = 8'h00; btbl[ 24] = 8'h4f;
	rtbl[ 25] = 8'h0d; gtbl[ 25] = 8'h00; btbl[ 25] = 8'h54;
	rtbl[ 26] = 8'h0e; gtbl[ 26] = 8'h00; btbl[ 26] = 8'h5a;
	rtbl[ 27] = 8'h0f; gtbl[ 27] = 8'h00; btbl[ 27] = 8'h60;
	rtbl[ 28] = 8'h10; gtbl[ 28] = 8'h00; btbl[ 28] = 8'h67;
	rtbl[ 29] = 8'h11; gtbl[ 29] = 8'h00; btbl[ 29] = 8'h6d;
	rtbl[ 30] = 8'h13; gtbl[ 30] = 8'h00; btbl[ 30] = 8'h73;
	rtbl[ 31] = 8'h14; gtbl[ 31] = 8'h00; btbl[ 31] = 8'h79;
	rtbl[ 32] = 8'h15; gtbl[ 32] = 8'h00; btbl[ 32] = 8'h7f;
	rtbl[ 33] = 8'h16; gtbl[ 33] = 8'h00; btbl[ 33] = 8'h86;
	rtbl[ 34] = 8'h18; gtbl[ 34] = 8'h00; btbl[ 34] = 8'h8c;
	rtbl[ 35] = 8'h19; gtbl[ 35] = 8'h00; btbl[ 35] = 8'h92;
	rtbl[ 36] = 8'h1b; gtbl[ 36] = 8'h00; btbl[ 36] = 8'h98;
	rtbl[ 37] = 8'h1c; gtbl[ 37] = 8'h00; btbl[ 37] = 8'h9f;
	rtbl[ 38] = 8'h1e; gtbl[ 38] = 8'h00; btbl[ 38] = 8'ha5;
	rtbl[ 39] = 8'h1f; gtbl[ 39] = 8'h00; btbl[ 39] = 8'hab;
	rtbl[ 40] = 8'h21; gtbl[ 40] = 8'h00; btbl[ 40] = 8'hb0;
	rtbl[ 41] = 8'h22; gtbl[ 41] = 8'h00; btbl[ 41] = 8'hb6;
	rtbl[ 42] = 8'h24; gtbl[ 42] = 8'h00; btbl[ 42] = 8'hbc;
	rtbl[ 43] = 8'h26; gtbl[ 43] = 8'h00; btbl[ 43] = 8'hc1;
	rtbl[ 44] = 8'h27; gtbl[ 44] = 8'h00; btbl[ 44] = 8'hc7;
	rtbl[ 45] = 8'h29; gtbl[ 45] = 8'h00; btbl[ 45] = 8'hcc;
	rtbl[ 46] = 8'h2b; gtbl[ 46] = 8'h00; btbl[ 46] = 8'hd1;
	rtbl[ 47] = 8'h2c; gtbl[ 47] = 8'h00; btbl[ 47] = 8'hd5;
	rtbl[ 48] = 8'h2e; gtbl[ 48] = 8'h00; btbl[ 48] = 8'hda;
	rtbl[ 49] = 8'h30; gtbl[ 49] = 8'h00; btbl[ 49] = 8'hde;
	rtbl[ 50] = 8'h32; gtbl[ 50] = 8'h00; btbl[ 50] = 8'he2;
	rtbl[ 51] = 8'h34; gtbl[ 51] = 8'h00; btbl[ 51] = 8'he6;
	rtbl[ 52] = 8'h36; gtbl[ 52] = 8'h00; btbl[ 52] = 8'hea;
	rtbl[ 53] = 8'h38; gtbl[ 53] = 8'h00; btbl[ 53] = 8'hed;
	rtbl[ 54] = 8'h3a; gtbl[ 54] = 8'h00; btbl[ 54] = 8'hf0;
	rtbl[ 55] = 8'h3c; gtbl[ 55] = 8'h00; btbl[ 55] = 8'hf3;
	rtbl[ 56] = 8'h3e; gtbl[ 56] = 8'h00; btbl[ 56] = 8'hf6;
	rtbl[ 57] = 8'h40; gtbl[ 57] = 8'h00; btbl[ 57] = 8'hf8;
	rtbl[ 58] = 8'h42; gtbl[ 58] = 8'h00; btbl[ 58] = 8'hfa;
	rtbl[ 59] = 8'h44; gtbl[ 59] = 8'h00; btbl[ 59] = 8'hfc;
	rtbl[ 60] = 8'h46; gtbl[ 60] = 8'h00; btbl[ 60] = 8'hfd;
	rtbl[ 61] = 8'h48; gtbl[ 61] = 8'h00; btbl[ 61] = 8'hfe;
	rtbl[ 62] = 8'h4a; gtbl[ 62] = 8'h00; btbl[ 62] = 8'hff;
	rtbl[ 63] = 8'h4c; gtbl[ 63] = 8'h00; btbl[ 63] = 8'hff;
	rtbl[ 64] = 8'h4f; gtbl[ 64] = 8'h00; btbl[ 64] = 8'hff;
	rtbl[ 65] = 8'h51; gtbl[ 65] = 8'h00; btbl[ 65] = 8'hff;
	rtbl[ 66] = 8'h53; gtbl[ 66] = 8'h00; btbl[ 66] = 8'hff;
	rtbl[ 67] = 8'h55; gtbl[ 67] = 8'h00; btbl[ 67] = 8'hfe;
	rtbl[ 68] = 8'h57; gtbl[ 68] = 8'h00; btbl[ 68] = 8'hfd;
	rtbl[ 69] = 8'h5a; gtbl[ 69] = 8'h00; btbl[ 69] = 8'hfc;
	rtbl[ 70] = 8'h5c; gtbl[ 70] = 8'h00; btbl[ 70] = 8'hfa;
	rtbl[ 71] = 8'h5e; gtbl[ 71] = 8'h00; btbl[ 71] = 8'hf8;
	rtbl[ 72] = 8'h60; gtbl[ 72] = 8'h00; btbl[ 72] = 8'hf6;
	rtbl[ 73] = 8'h63; gtbl[ 73] = 8'h00; btbl[ 73] = 8'hf3;
	rtbl[ 74] = 8'h65; gtbl[ 74] = 8'h00; btbl[ 74] = 8'hf0;
	rtbl[ 75] = 8'h67; gtbl[ 75] = 8'h00; btbl[ 75] = 8'hed;
	rtbl[ 76] = 8'h6a; gtbl[ 76] = 8'h00; btbl[ 76] = 8'hea;
	rtbl[ 77] = 8'h6c; gtbl[ 77] = 8'h00; btbl[ 77] = 8'he6;
	rtbl[ 78] = 8'h6e; gtbl[ 78] = 8'h00; btbl[ 78] = 8'he2;
	rtbl[ 79] = 8'h71; gtbl[ 79] = 8'h00; btbl[ 79] = 8'hde;
	rtbl[ 80] = 8'h73; gtbl[ 80] = 8'h00; btbl[ 80] = 8'hda;
	rtbl[ 81] = 8'h75; gtbl[ 81] = 8'h00; btbl[ 81] = 8'hd5;
	rtbl[ 82] = 8'h78; gtbl[ 82] = 8'h00; btbl[ 82] = 8'hd1;
	rtbl[ 83] = 8'h7a; gtbl[ 83] = 8'h00; btbl[ 83] = 8'hcc;
	rtbl[ 84] = 8'h7c; gtbl[ 84] = 8'h00; btbl[ 84] = 8'hc7;
	rtbl[ 85] = 8'h7f; gtbl[ 85] = 8'h00; btbl[ 85] = 8'hc1;
	rtbl[ 86] = 8'h81; gtbl[ 86] = 8'h00; btbl[ 86] = 8'hbc;
	rtbl[ 87] = 8'h83; gtbl[ 87] = 8'h00; btbl[ 87] = 8'hb6;
	rtbl[ 88] = 8'h86; gtbl[ 88] = 8'h00; btbl[ 88] = 8'hb0;
	rtbl[ 89] = 8'h88; gtbl[ 89] = 8'h00; btbl[ 89] = 8'hab;
	rtbl[ 90] = 8'h8a; gtbl[ 90] = 8'h00; btbl[ 90] = 8'ha5;
	rtbl[ 91] = 8'h8d; gtbl[ 91] = 8'h00; btbl[ 91] = 8'h9f;
	rtbl[ 92] = 8'h8f; gtbl[ 92] = 8'h00; btbl[ 92] = 8'h98;
	rtbl[ 93] = 8'h92; gtbl[ 93] = 8'h01; btbl[ 93] = 8'h92;
	rtbl[ 94] = 8'h94; gtbl[ 94] = 8'h01; btbl[ 94] = 8'h8c;
	rtbl[ 95] = 8'h96; gtbl[ 95] = 8'h02; btbl[ 95] = 8'h86;
	rtbl[ 96] = 8'h98; gtbl[ 96] = 8'h02; btbl[ 96] = 8'h7f;
	rtbl[ 97] = 8'h9b; gtbl[ 97] = 8'h02; btbl[ 97] = 8'h79;
	rtbl[ 98] = 8'h9d; gtbl[ 98] = 8'h03; btbl[ 98] = 8'h73;
	rtbl[ 99] = 8'h9f; gtbl[ 99] = 8'h04; btbl[ 99] = 8'h6d;
	rtbl[100] = 8'ha2; gtbl[100] = 8'h04; btbl[100] = 8'h67;
	rtbl[101] = 8'ha4; gtbl[101] = 8'h05; btbl[101] = 8'h60;
	rtbl[102] = 8'ha6; gtbl[102] = 8'h05; btbl[102] = 8'h5a;
	rtbl[103] = 8'ha8; gtbl[103] = 8'h06; btbl[103] = 8'h54;
	rtbl[104] = 8'hab; gtbl[104] = 8'h07; btbl[104] = 8'h4f;
	rtbl[105] = 8'had; gtbl[105] = 8'h08; btbl[105] = 8'h49;
	rtbl[106] = 8'haf; gtbl[106] = 8'h09; btbl[106] = 8'h43;
	rtbl[107] = 8'hb1; gtbl[107] = 8'h0a; btbl[107] = 8'h3e;
	rtbl[108] = 8'hb3; gtbl[108] = 8'h0a; btbl[108] = 8'h38;
	rtbl[109] = 8'hb6; gtbl[109] = 8'h0b; btbl[109] = 8'h33;
	rtbl[110] = 8'hb8; gtbl[110] = 8'h0c; btbl[110] = 8'h2e;
	rtbl[111] = 8'hba; gtbl[111] = 8'h0e; btbl[111] = 8'h2a;
	rtbl[112] = 8'hbc; gtbl[112] = 8'h0f; btbl[112] = 8'h25;
	rtbl[113] = 8'hbe; gtbl[113] = 8'h10; btbl[113] = 8'h21;
	rtbl[114] = 8'hc0; gtbl[114] = 8'h11; btbl[114] = 8'h1d;
	rtbl[115] = 8'hc2; gtbl[115] = 8'h12; btbl[115] = 8'h19;
	rtbl[116] = 8'hc4; gtbl[116] = 8'h13; btbl[116] = 8'h15;
	rtbl[117] = 8'hc6; gtbl[117] = 8'h15; btbl[117] = 8'h12;
	rtbl[118] = 8'hc8; gtbl[118] = 8'h16; btbl[118] = 8'h0f;
	rtbl[119] = 8'hca; gtbl[119] = 8'h17; btbl[119] = 8'h0c;
	rtbl[120] = 8'hcc; gtbl[120] = 8'h19; btbl[120] = 8'h09;
	rtbl[121] = 8'hce; gtbl[121] = 8'h1a; btbl[121] = 8'h07;
	rtbl[122] = 8'hcf; gtbl[122] = 8'h1c; btbl[122] = 8'h05;
	rtbl[123] = 8'hd1; gtbl[123] = 8'h1d; btbl[123] = 8'h03;
	rtbl[124] = 8'hd3; gtbl[124] = 8'h1f; btbl[124] = 8'h02;
	rtbl[125] = 8'hd5; gtbl[125] = 8'h20; btbl[125] = 8'h01;
	rtbl[126] = 8'hd7; gtbl[126] = 8'h22; btbl[126] = 8'h00;
	rtbl[127] = 8'hd8; gtbl[127] = 8'h23; btbl[127] = 8'h00;
	rtbl[128] = 8'hda; gtbl[128] = 8'h25; btbl[128] = 8'h00;
	rtbl[129] = 8'hdc; gtbl[129] = 8'h27; btbl[129] = 8'h00;
	rtbl[130] = 8'hdd; gtbl[130] = 8'h28; btbl[130] = 8'h00;
	rtbl[131] = 8'hdf; gtbl[131] = 8'h2a; btbl[131] = 8'h00;
	rtbl[132] = 8'he0; gtbl[132] = 8'h2c; btbl[132] = 8'h00;
	rtbl[133] = 8'he2; gtbl[133] = 8'h2e; btbl[133] = 8'h00;
	rtbl[134] = 8'he3; gtbl[134] = 8'h30; btbl[134] = 8'h00;
	rtbl[135] = 8'he5; gtbl[135] = 8'h31; btbl[135] = 8'h00;
	rtbl[136] = 8'he6; gtbl[136] = 8'h33; btbl[136] = 8'h00;
	rtbl[137] = 8'he8; gtbl[137] = 8'h35; btbl[137] = 8'h00;
	rtbl[138] = 8'he9; gtbl[138] = 8'h37; btbl[138] = 8'h00;
	rtbl[139] = 8'hea; gtbl[139] = 8'h39; btbl[139] = 8'h00;
	rtbl[140] = 8'hec; gtbl[140] = 8'h3b; btbl[140] = 8'h00;
	rtbl[141] = 8'hed; gtbl[141] = 8'h3d; btbl[141] = 8'h00;
	rtbl[142] = 8'hee; gtbl[142] = 8'h3f; btbl[142] = 8'h00;
	rtbl[143] = 8'hef; gtbl[143] = 8'h41; btbl[143] = 8'h00;
	rtbl[144] = 8'hf0; gtbl[144] = 8'h43; btbl[144] = 8'h00;
	rtbl[145] = 8'hf1; gtbl[145] = 8'h45; btbl[145] = 8'h00;
	rtbl[146] = 8'hf3; gtbl[146] = 8'h47; btbl[146] = 8'h00;
	rtbl[147] = 8'hf4; gtbl[147] = 8'h49; btbl[147] = 8'h00;
	rtbl[148] = 8'hf5; gtbl[148] = 8'h4c; btbl[148] = 8'h00;
	rtbl[149] = 8'hf5; gtbl[149] = 8'h4e; btbl[149] = 8'h00;
	rtbl[150] = 8'hf6; gtbl[150] = 8'h50; btbl[150] = 8'h00;
	rtbl[151] = 8'hf7; gtbl[151] = 8'h52; btbl[151] = 8'h00;
	rtbl[152] = 8'hf8; gtbl[152] = 8'h54; btbl[152] = 8'h00;
	rtbl[153] = 8'hf9; gtbl[153] = 8'h57; btbl[153] = 8'h00;
	rtbl[154] = 8'hfa; gtbl[154] = 8'h59; btbl[154] = 8'h00;
	rtbl[155] = 8'hfa; gtbl[155] = 8'h5b; btbl[155] = 8'h00;
	rtbl[156] = 8'hfb; gtbl[156] = 8'h5d; btbl[156] = 8'h00;
	rtbl[157] = 8'hfb; gtbl[157] = 8'h60; btbl[157] = 8'h00;
	rtbl[158] = 8'hfc; gtbl[158] = 8'h62; btbl[158] = 8'h00;
	rtbl[159] = 8'hfd; gtbl[159] = 8'h64; btbl[159] = 8'h00;
	rtbl[160] = 8'hfd; gtbl[160] = 8'h67; btbl[160] = 8'h00;
	rtbl[161] = 8'hfd; gtbl[161] = 8'h69; btbl[161] = 8'h00;
	rtbl[162] = 8'hfe; gtbl[162] = 8'h6b; btbl[162] = 8'h00;
	rtbl[163] = 8'hfe; gtbl[163] = 8'h6d; btbl[163] = 8'h00;
	rtbl[164] = 8'hff; gtbl[164] = 8'h70; btbl[164] = 8'h00;
	rtbl[165] = 8'hff; gtbl[165] = 8'h72; btbl[165] = 8'h00;
	rtbl[166] = 8'hff; gtbl[166] = 8'h75; btbl[166] = 8'h00;
	rtbl[167] = 8'hff; gtbl[167] = 8'h77; btbl[167] = 8'h00;
	rtbl[168] = 8'hff; gtbl[168] = 8'h79; btbl[168] = 8'h00;
	rtbl[169] = 8'hff; gtbl[169] = 8'h7c; btbl[169] = 8'h00;
	rtbl[170] = 8'hff; gtbl[170] = 8'h7e; btbl[170] = 8'h00;
	rtbl[171] = 8'hff; gtbl[171] = 8'h80; btbl[171] = 8'h00;
	rtbl[172] = 8'hff; gtbl[172] = 8'h83; btbl[172] = 8'h00;
	rtbl[173] = 8'hff; gtbl[173] = 8'h85; btbl[173] = 8'h00;
	rtbl[174] = 8'hff; gtbl[174] = 8'h87; btbl[174] = 8'h00;
	rtbl[175] = 8'hff; gtbl[175] = 8'h8a; btbl[175] = 8'h01;
	rtbl[176] = 8'hff; gtbl[176] = 8'h8c; btbl[176] = 8'h02;
	rtbl[177] = 8'hff; gtbl[177] = 8'h8e; btbl[177] = 8'h03;
	rtbl[178] = 8'hff; gtbl[178] = 8'h91; btbl[178] = 8'h04;
	rtbl[179] = 8'hff; gtbl[179] = 8'h93; btbl[179] = 8'h05;
	rtbl[180] = 8'hff; gtbl[180] = 8'h95; btbl[180] = 8'h07;
	rtbl[181] = 8'hff; gtbl[181] = 8'h98; btbl[181] = 8'h09;
	rtbl[182] = 8'hff; gtbl[182] = 8'h9a; btbl[182] = 8'h0a;
	rtbl[183] = 8'hff; gtbl[183] = 8'h9c; btbl[183] = 8'h0c;
	rtbl[184] = 8'hff; gtbl[184] = 8'h9f; btbl[184] = 8'h0f;
	rtbl[185] = 8'hff; gtbl[185] = 8'ha1; btbl[185] = 8'h11;
	rtbl[186] = 8'hff; gtbl[186] = 8'ha3; btbl[186] = 8'h13;
	rtbl[187] = 8'hff; gtbl[187] = 8'ha5; btbl[187] = 8'h16;
	rtbl[188] = 8'hff; gtbl[188] = 8'ha8; btbl[188] = 8'h19;
	rtbl[189] = 8'hff; gtbl[189] = 8'haa; btbl[189] = 8'h1c;
	rtbl[190] = 8'hff; gtbl[190] = 8'hac; btbl[190] = 8'h1f;
	rtbl[191] = 8'hff; gtbl[191] = 8'hae; btbl[191] = 8'h22;
	rtbl[192] = 8'hff; gtbl[192] = 8'hb0; btbl[192] = 8'h25;
	rtbl[193] = 8'hff; gtbl[193] = 8'hb3; btbl[193] = 8'h28;
	rtbl[194] = 8'hff; gtbl[194] = 8'hb5; btbl[194] = 8'h2c;
	rtbl[195] = 8'hff; gtbl[195] = 8'hb7; btbl[195] = 8'h30;
	rtbl[196] = 8'hff; gtbl[196] = 8'hb9; btbl[196] = 8'h33;
	rtbl[197] = 8'hff; gtbl[197] = 8'hbb; btbl[197] = 8'h37;
	rtbl[198] = 8'hff; gtbl[198] = 8'hbd; btbl[198] = 8'h3b;
	rtbl[199] = 8'hff; gtbl[199] = 8'hbf; btbl[199] = 8'h3f;
	rtbl[200] = 8'hff; gtbl[200] = 8'hc1; btbl[200] = 8'h43;
	rtbl[201] = 8'hff; gtbl[201] = 8'hc3; btbl[201] = 8'h47;
	rtbl[202] = 8'hff; gtbl[202] = 8'hc5; btbl[202] = 8'h4c;
	rtbl[203] = 8'hff; gtbl[203] = 8'hc7; btbl[203] = 8'h50;
	rtbl[204] = 8'hff; gtbl[204] = 8'hc9; btbl[204] = 8'h54;
	rtbl[205] = 8'hff; gtbl[205] = 8'hcb; btbl[205] = 8'h59;
	rtbl[206] = 8'hff; gtbl[206] = 8'hcd; btbl[206] = 8'h5d;
	rtbl[207] = 8'hff; gtbl[207] = 8'hcf; btbl[207] = 8'h62;
	rtbl[208] = 8'hff; gtbl[208] = 8'hd1; btbl[208] = 8'h67;
	rtbl[209] = 8'hff; gtbl[209] = 8'hd3; btbl[209] = 8'h6b;
	rtbl[210] = 8'hff; gtbl[210] = 8'hd4; btbl[210] = 8'h70;
	rtbl[211] = 8'hff; gtbl[211] = 8'hd6; btbl[211] = 8'h75;
	rtbl[212] = 8'hff; gtbl[212] = 8'hd8; btbl[212] = 8'h79;
	rtbl[213] = 8'hff; gtbl[213] = 8'hd9; btbl[213] = 8'h7e;
	rtbl[214] = 8'hff; gtbl[214] = 8'hdb; btbl[214] = 8'h83;
	rtbl[215] = 8'hff; gtbl[215] = 8'hdd; btbl[215] = 8'h87;
	rtbl[216] = 8'hff; gtbl[216] = 8'hde; btbl[216] = 8'h8c;
	rtbl[217] = 8'hff; gtbl[217] = 8'he0; btbl[217] = 8'h91;
	rtbl[218] = 8'hff; gtbl[218] = 8'he1; btbl[218] = 8'h95;
	rtbl[219] = 8'hff; gtbl[219] = 8'he3; btbl[219] = 8'h9a;
	rtbl[220] = 8'hff; gtbl[220] = 8'he4; btbl[220] = 8'h9f;
	rtbl[221] = 8'hff; gtbl[221] = 8'he6; btbl[221] = 8'ha3;
	rtbl[222] = 8'hff; gtbl[222] = 8'he7; btbl[222] = 8'ha8;
	rtbl[223] = 8'hff; gtbl[223] = 8'he9; btbl[223] = 8'hac;
	rtbl[224] = 8'hff; gtbl[224] = 8'hea; btbl[224] = 8'hb0;
	rtbl[225] = 8'hff; gtbl[225] = 8'heb; btbl[225] = 8'hb5;
	rtbl[226] = 8'hff; gtbl[226] = 8'hec; btbl[226] = 8'hb9;
	rtbl[227] = 8'hff; gtbl[227] = 8'hee; btbl[227] = 8'hbd;
	rtbl[228] = 8'hff; gtbl[228] = 8'hef; btbl[228] = 8'hc1;
	rtbl[229] = 8'hff; gtbl[229] = 8'hf0; btbl[229] = 8'hc5;
	rtbl[230] = 8'hff; gtbl[230] = 8'hf1; btbl[230] = 8'hc9;
	rtbl[231] = 8'hff; gtbl[231] = 8'hf2; btbl[231] = 8'hcd;
	rtbl[232] = 8'hff; gtbl[232] = 8'hf3; btbl[232] = 8'hd1;
	rtbl[233] = 8'hff; gtbl[233] = 8'hf4; btbl[233] = 8'hd4;
	rtbl[234] = 8'hff; gtbl[234] = 8'hf5; btbl[234] = 8'hd8;
	rtbl[235] = 8'hff; gtbl[235] = 8'hf6; btbl[235] = 8'hdb;
	rtbl[236] = 8'hff; gtbl[236] = 8'hf7; btbl[236] = 8'hde;
	rtbl[237] = 8'hff; gtbl[237] = 8'hf8; btbl[237] = 8'he1;
	rtbl[238] = 8'hff; gtbl[238] = 8'hf9; btbl[238] = 8'he4;
	rtbl[239] = 8'hff; gtbl[239] = 8'hf9; btbl[239] = 8'he7;
	rtbl[240] = 8'hff; gtbl[240] = 8'hfa; btbl[240] = 8'hea;
	rtbl[241] = 8'hff; gtbl[241] = 8'hfb; btbl[241] = 8'hec;
	rtbl[242] = 8'hff; gtbl[242] = 8'hfb; btbl[242] = 8'hef;
	rtbl[243] = 8'hff; gtbl[243] = 8'hfc; btbl[243] = 8'hf1;
	rtbl[244] = 8'hff; gtbl[244] = 8'hfc; btbl[244] = 8'hf3;
	rtbl[245] = 8'hff; gtbl[245] = 8'hfd; btbl[245] = 8'hf5;
	rtbl[246] = 8'hff; gtbl[246] = 8'hfd; btbl[246] = 8'hf7;
	rtbl[247] = 8'hff; gtbl[247] = 8'hfe; btbl[247] = 8'hf9;
	rtbl[248] = 8'hff; gtbl[248] = 8'hfe; btbl[248] = 8'hfa;
	rtbl[249] = 8'hff; gtbl[249] = 8'hfe; btbl[249] = 8'hfb;
	rtbl[250] = 8'hff; gtbl[250] = 8'hff; btbl[250] = 8'hfc;
	rtbl[251] = 8'hff; gtbl[251] = 8'hff; btbl[251] = 8'hfd;
	rtbl[252] = 8'hff; gtbl[252] = 8'hff; btbl[252] = 8'hfe;
	rtbl[253] = 8'hff; gtbl[253] = 8'hff; btbl[253] = 8'hff;
	rtbl[254] = 8'hff; gtbl[254] = 8'hff; btbl[254] = 8'hff;
	end
	// }}}
endmodule
