////////////////////////////////////////////////////////////////////////////////
//
// Filename:	vgasim.cpp
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	This is the main simulator source code file.  It uses gtkmm
//		to create both an off-screen drawing area, as well as a 
//	DrawingArea to display the "image" sent from the Verilog code to the
//	slave/output "monitor".
//
//	There is also a window class that holds this VGA simulation, called
//	VGAWIN.  This is a top level window with just the one child, the
//	simulation window.
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
#include <stdio.h>
#include <stdlib.h>

#include <gtkmm.h>

#include "vgasim.h"
#include "image.cpp"

const	int	VGASIM::CLOCKS_PER_PIXEL = 1,
		VGASIM::BITS_PER_COLOR=8;
const	bool	VGASIM::m_debug = false;

void	VGASIM::on_realize() {
	Gtk::DrawingArea::on_realize();

	// if (m_debug) printf("ON-REALIZE\n");
	m_pix = Cairo::ImageSurface::create(Cairo::FORMAT_RGB24,
		m_mode.width(), m_mode.height());
	m_gc  = Cairo::Context::create(m_pix);

	m_gc->set_source_rgb(0.0,0.0,0.0);
	m_gc->rectangle(0, 0, m_mode.width(), m_mode.height());
	m_gc->fill();
};

void	VGASIM::get_preferred_width_vfunc(int &min, int &nw) const {
	min = m_mode.width(); nw = m_mode.width();
} void	VGASIM::get_preferred_width_for_height_vfunc(int h, int &min, int &nw) const {
	min = m_mode.width(); nw = m_mode.width();
}

void	VGASIM::get_preferred_height_vfunc(int &min, int &nw) const {
	min = m_mode.height(); nw = m_mode.height();
}
void	VGASIM::get_preferred_height_for_width_vfunc(int w, int &min, int &nw) const {
	min = m_mode.height(); nw = m_mode.height();
}

void	VGASIM::operator()(const int vsync, const int hsync, const int r, const int g, const int b) {
	int	xv, yv;

	if ((m_debug)&&(m_out_of_sync))
		printf("VGASIM--TICK(%d,%d,%6d,%6d)\r", vsync, hsync, m_vsync_count, m_hsync_count);

	if (++m_pixel_clock_count < CLOCKS_PER_PIXEL) {
		bool	not_same = false;
		if (vsync != m_last_vsync)
			not_same = true;
		else if (hsync != m_last_hsync)
			not_same = true;
		else if (r != m_last_r)
			not_same = true;
		else if (g != m_last_g)
			not_same = true;
		else if (b != m_last_b)
			not_same = true;
		if (not_same) {
			if (!m_out_of_sync)
				printf("%30s\n", "PX-RESYNC");
			m_pixel_clock_count = 0;
			m_out_of_sync = true;
		}
	} else {
		m_pixel_clock_count = 0;

		if ((!vsync)&&(m_last_vsync)) {
			//
			// On the first time vsync is dropped, we'll declare
			// this to be the beginning of the synchronization
			// period
			//
			if ((m_vsync_count != 0)
				&&(m_vsync_count != m_mode.raw_width() * m_mode.raw_height()-1)) {
				// Lose synch
				m_out_of_sync = true;
				printf("%30s (%d, %d)\n", "V-RESYNC",
					m_vsync_count,
					m_mode.raw_width() * m_mode.sync_lines()-1);
			} else if (m_debug)
				printf("\nVGA-FRAME\n");

			m_vsync_count = 0;
			m_out_of_sync = false;
			if ((m_hsync_count != m_mode.raw_width())&&(!m_out_of_sync)) {
				m_vsync_count = 0;
				// printf("H-RESYNC(V)\n");
				// m_out_of_sync = true;
			}

		} else if (!vsync) {
			//
			// Count the number of clocks with vsync false
			//
			// These would be during the vertical sync pulse,
			// since it is active low.  There should be
			// m_mode.sync_lines() lines of this pulse being high.
			//
			if (m_vsync_count < m_mode.sync_lines()*m_mode.raw_width() - 1)
				m_vsync_count++;
			else {
				// If we've got too many of them, then
				// declare us to be out of synch.
				if (!m_out_of_sync) {
					m_out_of_sync = true;
					printf("%30s (%d, %d)\n", "V-RESYNC (TOO MANY)",
					m_vsync_count,
					m_mode.raw_width() * m_mode.sync_lines()-1);
				}
				m_vsync_count = m_mode.sync_lines()*m_mode.raw_width() - 1;
			}
		} else
			m_vsync_count++;

		if ((!hsync)&&(m_last_hsync)) {
			// On the first hsync pulse, we start counting pixels.
			// There should be exactly raw_width() pixels per line.
			if ((m_hsync_count != m_mode.raw_width()-1)&&(!m_out_of_sync)) {
				m_vsync_count = 0;
				printf("H-RESYNC\n");
				printf("\n%30s (%d,%d)\n","H-RESYNC (Wrong #)", m_hsync_count, m_mode.raw_width());
				m_out_of_sync = true;
			}

			m_hsync_count = 0;
		} else if (!hsync) {
			// During the horizontal sync, we expect m_mode.sync_pixels()
			// pixels with the hsync low.
			if (m_hsync_count < m_mode.sync_pixels() - 1)
				m_hsync_count++;
			else {
				// Too many pixels with m_mode.sync_pixels()
				// low, and we are out of synch.
				m_hsync_count = m_mode.sync_pixels() - 1;
				if (!m_out_of_sync) {
					m_vsync_count = 0;
					printf("\n%30s (%d,%d)\n","H-RESYNC (TOO-MANY)", m_hsync_count, m_mode.raw_width());
					m_out_of_sync = true;
				}
			}
		} else
			// Otherwise .... just count horizontal pixels
			// from the first synch pixel
			m_hsync_count++;

		assert((m_vsync_count <   m_mode.sync_lines() * m_mode.raw_width())||(vsync));
		assert( m_vsync_count <   m_mode.raw_height()*m_mode.raw_width());
		assert((m_hsync_count <   m_mode.sync_pixels())||(hsync));
		assert( m_hsync_count <   m_mode.raw_width());


		yv = (m_vsync_count-m_hsync_count)/m_mode.raw_width();
		yv -= m_mode.vback_porch() + m_mode.sync_lines();
		xv = (m_hsync_count) -(m_mode.sync_pixels() + m_mode.hback_porch());

		if ((xv >= 0)&&(yv >= 0) // only if in range
				&&(xv < m_mode.width())&&(yv < m_mode.height())
				&&(!m_out_of_sync)) {
			unsigned	clr, msk = (1<<BITS_PER_COLOR)-1;

			clr = ((r&msk)<<(24-BITS_PER_COLOR))
					|((g&msk)<<(16-BITS_PER_COLOR))
					|((b & msk)<<(8-BITS_PER_COLOR));
			if (m_data->m_img[yv][xv] != clr) {
				m_data->m_img[yv][xv] = clr;
	
				// printf("\nIMG[%03d][%03d] = %03x\n",
				//		yv, xv, clr);
				m_gc->set_source_rgb(
					(r&msk)/(double)(msk),
					(g&msk)/((double)msk),
					(b&msk)/((double)msk));
				m_gc->rectangle(xv, yv, 1, 1);
				m_gc->fill();
				
				queue_draw_area(xv, yv, 1, 1);
				// m_window->invalidate_rect(Gdk::Rectangle(
				// 	xv, yv, 1, 1), true);
			}
		} // else if (!m_out_of_sync)
		//	printf("IMG[%03d][%03d] (Out-of-bounds)\n", yv, xv);
	}

	m_last_vsync = vsync;
	m_last_hsync = hsync;
	m_last_r     = r;
	m_last_g     = g;
	m_last_b     = b;
}

bool	VGASIM::on_draw(CONTEXT &gc) {
	// printf("ON-DRAW\n");
	gc->save();
	// gc->rectangle(0,0,VGA_WIDTH, VGA_HEIGHT);
	// gc->clip();
	gc->set_source(m_pix, 0, 0);
	gc->paint();
	gc->restore();

	return true;
}

void	VGAWIN::init(void) {

	m_vgasim->set_size_request(m_vgasim->width(),m_vgasim->height());
	set_border_width(0);
	add(*m_vgasim);
	show_all();
	Gtk::Window::set_title(Glib::ustring("VGA Simulator"));
};

VGAWIN::VGAWIN(void) {
	m_vgasim = new VGASIM(640, 480);
	init();
}

VGAWIN::VGAWIN(const int w, const int h) {
	m_vgasim = new VGASIM(w, h);
	init();
}

VGAWIN::VGAWIN(const char *h, const char *v) {
	m_vgasim = new VGASIM(h, v);
	init();
}

