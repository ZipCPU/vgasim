////////////////////////////////////////////////////////////////////////////////
//
// Filename:	vgasource.h
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
#ifndef	VGASOURCE_H
#define	VGASOURCE_H

#include <stdio.h>
#include <assert.h>
//
#include <gtk/gtk.h>
#include <gtkmm.h>
#include <gdk/gdk.h>
//
#include "videomode.h"

class	VGASOURCE {
	GdkPixbuf	*m_image;
	GdkWindow	*m_root_window;
	gint		m_root_width, m_root_height;
	gint		m_xoffset, m_yoffset;
	int		m_xpos, m_ypos;
	const int	SYNC_ACTIVE = 0, SYNC_INACTIVE = 1;
	VIDEOMODE	m_mode;
	int		m_bytes_per_pixel;

	void	init(void);

public:
	VGASOURCE(VIDEOMODE m) : m_mode(m) {
		init();
	}

	VGASOURCE(const int w, const int h) : m_mode(w,h) {
		init();
	}

	VGASOURCE(const char *h, const char *v) : m_mode(h, v) {
		init();
	}

	void	get_screenshot(void);
	void	operator()(int &vsync, int &hsync,
			int &red, int &green, int &blue);
};
#endif
