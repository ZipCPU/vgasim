////////////////////////////////////////////////////////////////////////////////
//
// Filename:	hdmisource.cpp
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	This is the HDMI source simulator file.  It uses the top left
// 		area of your screen as a source to create a vertical and
// 	horizontal sync and pixels from.  These can then be fed into a
// 	Verilator (or other) based simulation.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2020, Gisselquist Technology, LLC
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
#include "hdmisource.h"

// #define	VIDEO_GUARD	0
// #define	VIDEO_DATA	1
// #define	CTL_PERIOD	2
// #define	DATA_GUARD	3
// #define	DATA_ISLAND	4

const int	DTYP_GUARD_BAND     = 0,
		DTYP_CONTROL_PERIOD = 1,
		DTYP_DATA_ISLAND    = 2,
		DTYP_PIXEL_DATA     = 3;

int	TMDSENCODER::countones(int word) {
	int	k, w = word, c = 0;

	for(k = 0; k<10; k++) {
		c += (w&1);
		w>>=1;
	}

	return c;
}

int	TMDSENCODER::bitreverse(int val) {
	int	result = 0, tmp = val;

	for(int k=0; k<10; k++) {
		result <<= 1;
		result |= (tmp&1);
		tmp >>= 1;
	}

	return result;
}


int	TMDSENCODER::ctldata(int ctl) {
	int	word = 0;

	switch(ctl&3) {
	case 0: word = bitreverse(0x354); break;
	case 1: word = bitreverse(0x0ab); break;
	case 2: word = bitreverse(0x154); break;
	case 3: word = bitreverse(0x2ab); break;
	}

	return word;
}

int	TMDSENCODER::pixeldata(int pix) {
	int	word, tmp;

	// This isn't quite right, since it's not guaranteed
	// to be balanced as desired
	word = (pix & 0x01);
	word |= (pix ^ (word << 1)) & 0x02;
	word |= (pix ^ (word << 1)) & 0x04;
	word |= (pix ^ (word << 1)) & 0x08;
	word |= (pix ^ (word << 1)) & 0x10;
	word |= (pix ^ (word << 1)) & 0x20;
	word |= (pix ^ (word << 1)) & 0x40;
	word |= (pix ^ (word << 1)) & 0x80;

	tmp = countones(pix & 0x0ff);
	if ((tmp > 4)||(tmp == 4 && (pix & 0x080)))
		word ^= 0x0aa;
	else
		word ^= 0x100;
	if ((m_count ==0)||(countones(word & 0x0ff) == 4)) {
		if (word & 0x0100) {
			m_count = m_count - (2*countones(word & 0x0ff) - 8);
		} else {
			word ^= 0x02ff;
			m_count = m_count + 2*countones(word & 0x0ff) - 8;
		}
	} else if ((m_count > 0 && (tmp > 4))
			||(m_count < 0 && (tmp < 4))) {
		m_count = m_count + ((word & 0x100) ? 2 : 0)
			- 2*countones(word & 0x0ff)+8;
		word ^= 0x2ff;
	} else {
		m_count = m_count - ((word & 0x100) ? 0 : 2)
			+ 2*countones(word & 0x0ff)-8;
	}

	return bitreverse(word);
}

int	TMDSENCODER::apply(int dtype, int ctl, int aux, int data) {
	int	word = 0;

	switch(dtype) {
	case DTYP_GUARD_BAND:
		return guard();
		break;
	case DTYP_CONTROL_PERIOD:
		return ctldata(ctl);
		break;
	case DTYP_DATA_ISLAND:
		switch(aux&0x0f) {
		case 0x0: word = 0x29c; break;
		case 0x1: word = 0x263; break;
		case 0x2: word = 0x2e4; break;
		case 0x3: word = 0x2e2; break;
		//
		case 0x4: word = 0x171; break;
		case 0x5: word = 0x11e; break;
		case 0x6: word = 0x14e; break;
		case 0x7: word = 0x13c; break;
		//
		case 0x8: word = 0x2cc; break;
		case 0x9: word = 0x139; break;
		case 0xa: word = 0x19c; break;
		case 0xb: word = 0x2c6; break;
		//
		case 0xc: word = 0x28e; break;
		case 0xd: word = 0x271; break;
		case 0xe: word = 0x163; break;
		case 0xf: word = 0x2c3; break;
		} break;
	case DTYP_PIXEL_DATA:
		return pixeldata(data);
		break;
	default:
		// Break protocol--we should never get here
		word = 0;
		assert(0);
		break;
	}

	return bitreverse(word);
}


void	HDMISOURCE::init(void) {
	m_root_window = gdk_get_default_root_window();
	m_xoffset = m_yoffset = 0;

	m_bytes_per_pixel = 3;
	m_image = NULL;
	get_screenshot();
	m_xpos = m_ypos = 0;

	// Initialize the TMDS encoder with a known state
	m_lastblu = 0;
	m_lastgrn = 0;
	m_lastred = 0;
}

void	HDMISOURCE::get_screenshot(void) {
	// Glib::RefPtr<Gdk::Pixbuf> image = Gdk::Pixbuf::... ??
	// Gdk::Cairo::set_source_pixbuf(cr, image, ?, ?);
	//

	// m_image = new Gdk::Pixbuf(m_root_window, m_xoffset, m_yoffset, m_mode.width(), m_mode.height());

	m_image = gdk_pixbuf_get_from_window(m_root_window,
			m_xoffset, m_yoffset, m_mode.width(), m_mode.height());
	g_assert( gdk_pixbuf_get_n_channels(m_image) == 3);
	g_assert(!gdk_pixbuf_get_has_alpha(m_image));
	g_assert( gdk_pixbuf_get_bits_per_sample(m_image) == 8);
	g_assert(gdk_pixbuf_get_colorspace(m_image) == GDK_COLORSPACE_RGB);
}

void	HDMISOURCE::operator()(int &blu, int &grn, int &red) {
	int	pxblue, pxgreen, pxred, hsync, vsync;

	m_xpos++;
	if (m_xpos >= m_mode.raw_width()) {
		m_xpos = 0;
		m_ypos++;
		if (m_ypos >= m_mode.raw_height()) {
			m_ypos = 0;
			get_screenshot();
		}
	}

	assert(m_xpos < m_mode.raw_width());
	assert(m_ypos < m_mode.raw_height());

	// [ WIDTH BACK PORCH SYNC PIXELS FRONT PORCH ]
	hsync = SYNC_INACTIVE; vsync = SYNC_INACTIVE;
	if ((m_xpos < m_mode.width())&&(m_ypos < m_mode.height())) {
		int	stride = gdk_pixbuf_get_rowstride(m_image);

		guchar *raw, *line, *pixel;
		raw = gdk_pixbuf_get_pixels(m_image);
		line = raw + (stride * m_ypos);
		pixel= line + (m_bytes_per_pixel * m_xpos);

		pxred    = (*pixel++) & 0x0ff;
		pxgreen  = (*pixel++) & 0x0ff;
		pxblue   = (*pixel) & 0x0ff;

		blu = tmdsblu.pixeldata(pxblue);
		grn = tmdsgrn.pixeldata(pxgreen);
		red = tmdsred.pixeldata(pxred);
	} else {
		pxred    = 0;
		pxgreen  = 0;
		pxblue   = 0;

		if ((m_xpos >= m_mode.hporch())
			  &&(m_xpos < m_mode.hporch() + m_mode.sync_pixels())) {
			hsync = SYNC_ACTIVE;
		}

		if ((m_ypos >= m_mode.vporch())
			  &&(m_ypos < m_mode.vporch() + m_mode.sync_lines())) {
			vsync = SYNC_ACTIVE;
		}

#define	PREPIXEL_GUARD	2	// From the HDMI spec, must be 2 pixels
#define	PREPIXEL_PREAMBLE	8+PREPIXEL_GUARD // 8 pixels before the guard

		if ((m_xpos >= m_mode.raw_width()-PREPIXEL_GUARD)
			&&((m_ypos < m_mode.height()-1)
				||(m_ypos == m_mode.raw_height() - 1))) {
			blu = tmdsblu.guard();
			grn = tmdsgrn.guard();
			red = tmdsred.guard();
		} else if ((m_xpos >= m_mode.raw_width()-PREPIXEL_PREAMBLE)
			&&((m_ypos < m_mode.height()-1)
				||(m_ypos == m_mode.raw_height() - 1))) {
			blu = tmdsblu.ctldata(0);
			grn = tmdsgrn.ctldata(2);
			red = tmdsred.ctldata(2);
		} else {
			int	control = (vsync << 1) | hsync;

			blu = tmdsblu.ctldata(control);
			grn = tmdsgrn.ctldata(1);
			red = tmdsred.ctldata(0);
		}
	}
}
