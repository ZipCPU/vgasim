////////////////////////////////////////////////////////////////////////////////
//
// Filename:	simcheck.cpp
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	This is a basic test bench for the VGA source and simulator
//		together.  It doesn't use verilator, but rather proves that
//	the VGA source can actually create a valid source for a verilator based
//	project.  To do this, the VGASOURCE is fed directly into the VGASIM,
//	creating a test window/image on your display that demonstrates this
//	capability.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018, Gisselquist Technology, LLC
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
#include <signal.h>
#include <time.h>
#include <ctype.h>

#include <verilated.h>

#include "testb.h"
// #include "twoc.h"
#include "vgasim.h"
#include "vgasource.h"


// No particular "parameters" need definition or redefinition here.
class	TESTBENCH {
public:
	VGAWIN		m_vga;
	VGASOURCE	m_src;

	TESTBENCH(void) : m_vga(640, 480), m_src(640, 480)
			// m_vga(1280, 1024)
			// m_vga(1280,720)
			{
		//
		Glib::signal_idle().connect(
				sigc::mem_fun((*this),&TESTBENCH::on_tick));
	}

	void	tick(void) {

		/*
		if ((m_tickcount & ((1<<28)-1))==0) {
			double	ticks_per_second = m_tickcount;
			time_t	seconds_passed = time(NULL)-m_start_time;
			if (seconds_passed != 0) {
			ticks_per_second /= (double)(time(NULL) - m_start_time);
			printf(" ********   %.6f TICKS PER SECOND\n", 
				ticks_per_second);
			}
		}
		*/

		int	vsync, hsync, red, green, blue;
		m_src(vsync, hsync, red, green, blue);
		m_vga(vsync, hsync, red, green, blue);
	}

	bool	on_tick(void) {
		for(int i=0; i<5; i++)
			tick();
		return true;
	}
};

TESTBENCH	*tb;

int	main(int argc, char **argv) {
	Gtk::Main	main_instance(argc, argv);

	tb = new TESTBENCH();

	// tb->opentrace("vga.vcd");
	Gtk::Main::run(tb->m_vga);

	exit(0);
}

