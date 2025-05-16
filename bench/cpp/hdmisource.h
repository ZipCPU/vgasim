////////////////////////////////////////////////////////////////////////////////
//
// Filename:	bench/cpp/hdmisource.h
// {{{
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
// }}}
// Copyright (C) 2020-2025, Gisselquist Technology, LLC
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
// }}}
#ifndef	HDMISOURCE_H
#define	HDMISOURCE_H

#include <stdio.h>
#include <assert.h>
//
#include <gtk/gtk.h>
#include <gtkmm.h>
#include <gdk/gdk.h>
#include "image.h"
#include "videomode.h"
// #include "simwin.h"

#define	VIDEO_GUARD	0
#define	VIDEO_DATA	1
#define	CTL_PERIOD	2
#define	DATA_GUARD	3
#define	DATA_ISLAND	4
#define	HDMI_LOST	5

extern	int	gbl_nframes;

class	TMDSENCODER {
	int	m_count, m_guard;

public:
	TMDSENCODER(int channel) {
		m_count = 0;

		switch(channel) {
		case 0: m_guard = 0x2cc;	break;
		case 1: m_guard = 0x133;	break;
		default:
			m_guard = 0x2cc;
		}
	}

	int	countones(int word);
	int	apply(int dtype, int ctl, int aux, int data);
	int	operator()(int dtype, int ctl, int aux, int data) {
		return apply(dtype, ctl, aux, data);
	}
	int	guard(void) { return bitreverse(m_guard); };
	int	pixeldata(int p);
	int	ctldata(int c);
	int	bitreverse(int val);
};

class	HDMISOURCE {
	GdkPixbuf	*m_image;
	GdkWindow	*m_root_window;
	gint		m_root_width, m_root_height;
	gint		m_xoffset, m_yoffset;
	int		m_xpos, m_ypos;
	const int	SYNC_ACTIVE = 1, SYNC_INACTIVE = 0;
	VIDEOMODE	m_mode;
	int		m_bytes_per_pixel;
	int		m_lastblu, m_lastgrn, m_lastred;
	TMDSENCODER	tmdsblu, tmdsgrn, tmdsred;

	void	init(void);

public:

	HDMISOURCE(VIDEOMODE m) : m_mode(m), tmdsblu(0), tmdsgrn(1), tmdsred(2) {
		init();
	}

	HDMISOURCE(const int w, const int h) : m_mode(w,h), tmdsblu(0), tmdsgrn(1), tmdsred(2) {
		init();
	}

	HDMISOURCE(const char *h, const char *v) : m_mode(h, v), tmdsblu(0), tmdsgrn(1), tmdsred(2) {
		init();
	}

	void	get_screenshot(void);
	void	operator()(int &red, int &green, int &blue);
};
#endif
