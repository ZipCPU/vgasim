////////////////////////////////////////////////////////////////////////////////
//
// Filename:	hdmisim.h
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2018-2022, Gisselquist Technology, LLC
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
#ifndef	HDMISIM_H
#define	HDMISIM_H

#include <gtkmm.h>
#include "image.h"
#include "videomode.h"
#include "simwin.h"

class	HDMISIM : public Gtk::DrawingArea {
public:
	// Type definitions ... just to make using these types easier and
	// simpler on the fingers.
	typedef	Cairo::RefPtr<Cairo::Context>		CAIROGC;
	typedef	const Cairo::RefPtr<Cairo::Context>	CONTEXT;
	typedef	Cairo::RefPtr<Cairo::ImageSurface>	CAIROIMG;

	static	const	bool	m_debug;

	CAIROIMG		m_pix;
	CAIROGC			m_gc;
	IMAGE<unsigned>		*m_data;
	VIDEOMODE		m_mode;
	bool	m_out_of_sync;

	int	m_last_vsync, m_last_hsync, m_last_r, m_last_g, m_last_b,
		m_pixel_clock_count;
	int	m_state, m_state_counter;
	int	m_vsync_count, m_hsync_count;

	void	initialize(void) {
		m_data = new IMAGE<unsigned>(m_mode.height(), m_mode.width());
		m_data->zeroize();

		m_vsync_count = 0;
		m_hsync_count = 0;

		set_has_window(true);
		Widget::set_can_focus(false);
		set_size_request(m_mode.width(), m_mode.height());

		m_state = 2; // CTL_PERIOD;
		m_state_counter = 0;

		m_out_of_sync = true;
	}

public:
	static	const	int	CLOCKS_PER_PIXEL,
				BITS_PER_COLOR;

	static	int	bitreverse(int val);
	static	bool	isguard(int val);
	static	int	ctldata(int val);
	static	int	pktdata(int val);
	static	int	pixeldata(int val);



	HDMISIM(void) : Gtk::DrawingArea(), m_mode(640,480) {
		initialize();
	}

	HDMISIM(const int w, const int h) : Gtk::DrawingArea(), m_mode(w, h) {
		initialize();
	}

	HDMISIM(const char *h, const char *v) : Gtk::DrawingArea(), m_mode(h,v) {
		initialize();
	}

	void	get_preferred_width_vfunc(int &min, int &nw) const;
	void	get_preferred_height_vfunc(int &min, int &nw) const;
	void	get_preferred_height_for_width_vfunc(int w, int &min, int &nw) const;
	void	get_preferred_width_for_height_vfunc(int w, int &min, int &nw) const;

	virtual	void	on_realize();

	void	operator()(const int blu, const int grn, const int red);
	virtual	bool	on_draw(CONTEXT &gc);
	bool	syncd(void) { return !m_out_of_sync; }
};

class	HDMIWIN	: public SIMWIN {
private:

	void	init(void);
public:
	HDMISIM	*m_hdmisim;
	HDMIWIN(void);
	HDMIWIN(const int w, const int h);
	HDMIWIN(const char *h, const char *v);
	~HDMIWIN(void) { delete m_hdmisim; }
	void	operator()(const int blu, const int grn, const int red) {
		(*m_hdmisim)(blu,grn,red);
	}
	bool	syncd(void) const { return m_hdmisim->syncd(); }
};

#endif

