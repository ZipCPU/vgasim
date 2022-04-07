////////////////////////////////////////////////////////////////////////////////
//
// Filename:	vgasource.cpp
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	This is the VGA source simulator file.  It uses the top left
// 		area of your screen as a source to create a vertical and
// 	horizontal sync and pixels from.  These can then be fed into a
// 	Verilator (or other) based simulation.
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
#include "vgasource.h"

void	VGASOURCE::init(void) {
	m_root_window = gdk_get_default_root_window();
	// gdk_drawable_get_size(m_root_window,
	//		&m_root_width, &m_root_height);
	m_xoffset = m_yoffset = 0;

	// g_assert(gdk_pixbuf_get_colorspace(m_root_window)
	//			== GDK_COLORSPACE_RGB);
	m_bytes_per_pixel = 3;
	m_image = NULL;
	get_screenshot();
	m_xpos = m_ypos = 0;
}

void	VGASOURCE::get_screenshot(void) {
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

void	VGASOURCE::operator()(int &vsync, int &hsync,
			int &red, int &green, int &blue) {
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

		if (m_bytes_per_pixel == 3) {
			red    = (*pixel++) & 0x0ff;
			green  = (*pixel++) & 0x0ff;
			blue   = (*pixel) & 0x0ff;
		} else if (m_bytes_per_pixel == 4) {
			red    = (*++pixel) & 0x0ff;
			green  = (*++pixel) & 0x0ff;
			blue   = (*++pixel) & 0x0ff;
		}

	} else {
		if ((m_xpos >= m_mode.hporch())
			  &&(m_xpos < m_mode.hporch() + m_mode.sync_pixels())) {
			hsync = SYNC_ACTIVE;
		}

		if ((m_ypos >= m_mode.vporch())
			  &&(m_ypos < m_mode.vporch() + m_mode.sync_lines())) {
			vsync = SYNC_ACTIVE;
		}
	}
}
