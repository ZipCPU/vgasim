////////////////////////////////////////////////////////////////////////////////
//
// Filename:	simwin.h
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
#ifndef	SIMWIN_H
#define	SIMWIN_H

#include <gtkmm.h>
#include "image.h"
#include "videomode.h"

class	SIMWIN	: public Gtk::Window {
protected:
	VIDEOMODE	m_vmode;

public:
	SIMWIN(void) : m_vmode(640,480) {};
	SIMWIN(const int w, const int h) : m_vmode(w,h) {};
	SIMWIN(const char *h, const char *v) : m_vmode(h,v) {};

	virtual	bool syncd(void)  const= 0;

	int  width(void)  const {
		return m_vmode.width();
	}

	int  height(void) const {
		return	m_vmode.height();
	}

	int  raw_width(void)  const {
		return m_vmode.raw_width();
	}

	int  raw_height(void) const {
		return m_vmode.raw_height();
	}
	int  hsync(void)  const {
		return	m_vmode.hsync();
	}
	int  vsync(void)  const {
		return	m_vmode.vsync();
	}
	int hporch(void)  const {
		return	m_vmode.hporch();
	}
	int vporch(void)  const {
		return	m_vmode.vporch();
	}
	int clocks_per_frame(void) const {
		return	m_vmode.pixels_per_frame();
	}
};

#endif
