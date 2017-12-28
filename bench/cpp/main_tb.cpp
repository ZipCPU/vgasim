////////////////////////////////////////////////////////////////////////////////
//
// Filename:	main_tb.cpp
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	This is the main test bench class that holds all the pieces
//		together.  In this case, the test bench consists of little
//	more than a video simulator.
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
#include <signal.h>
#include <time.h>
#include <ctype.h>

#include "verilated.h"
#include "Vwbvgaframe.h"

#include "testb.h"
// #include "twoc.h"
#include "vgasim.h"

#ifdef	NEW_VERILATOR
#define	VVAR(A)	busmaster__DOT_ ## A
#else
#define	VVAR(A)	v__DOT_ ## A
#endif

// #define	wb_err		VVAR(_wb_err)
//
//
#define	wbubus_ack	VVAR(___Vcellinp__genbus____pinNumber9)
#define	wbubus_stall	VVAR(___Vcellinp__genbus____pinNumber10)

// No particular "parameters" need definition or redefinition here.
class	TESTBENCH : public TESTB<Vwbvgaframe> {
public:
	unsigned long	m_tx_busy_count;
	VGAWIN		m_vga;
	bool		m_done;

	TESTBENCH(void) : m_vga(1280,720) {
		//
		m_core->i_hm_width  = m_vga.width();
		m_core->i_hm_porch  = m_vga.hporch();
		m_core->i_hm_synch  = m_vga.hsync();
		m_core->i_hm_raw    = m_vga.raw_width();
		//
		m_core->i_vm_height = m_vga.height();
		m_core->i_vm_porch  = m_vga.vporch();
		m_core->i_vm_synch  = m_vga.vsync();
		m_core->i_vm_raw    = m_vga.raw_height();
		//
		m_core->i_test      = 1;
		//
		m_done = false;

		Glib::signal_idle().connect(sigc::mem_fun((*this),&TESTBENCH::on_tick));
	}

	void	trace(const char *vcd_trace_file_name) {
		fprintf(stderr, "Opening TRACE(%s)\n", vcd_trace_file_name);
		opentrace(vcd_trace_file_name);
	}

	void	close(void) {
		// TESTB<BASECLASS>::closetrace();
		m_done = true;
	}

	void	tick(void) {
		if (m_done)
			return;

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

		m_vga((m_core->o_vga_vsync)?0:1, (m_core->o_vga_hsync)?0:1,
			m_core->o_vga_red,
			m_core->o_vga_grn,
			m_core->o_vga_blu);

		TESTB<Vwbvgaframe>::tick();
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
	Verilated::commandArgs(argc, argv);

	tb = new TESTBENCH();
	tb->reset();

	// tb->opentrace("vga.vcd");
	Gtk::Main::run(tb->m_vga);

	exit(0);
}

