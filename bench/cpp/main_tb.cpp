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
// Copyright (C) 2017-2022, Gisselquist Technology, LLC
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
#include <unistd.h>

#include "verilated.h"
#include "Vdemo.h"

#include "testb.h"
// #include "twoc.h"
#include "vgasim.h"

#ifdef	NEW_VERILATOR
#define	VVAR(A)	busmaster__DOT_ ## A
#else
#define	VVAR(A)	v__DOT_ ## A
#endif


// No particular "parameters" need definition or redefinition here.
class	TESTBENCH : public TESTB<Vdemo> {
private:
	unsigned long	m_tx_busy_count;
	bool		m_done, m_test;
public:
	VGAWIN		m_vga;
private:

	void	init(void) {
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
		m_core->i_test      = (m_test) ? 1 : 0;
		//
		m_done = false;

		Glib::signal_idle().connect(sigc::mem_fun((*this),&TESTBENCH::on_tick));
	}
public:

	TESTBENCH(void) : m_test(false), m_vga(1280, 1024) {
		init();
	}

	TESTBENCH(int hres, int vres) : m_test(false), m_vga(hres, vres) {
		init();
	}

	void	trace(const char *vcd_trace_file_name) {
		fprintf(stderr, "Opening TRACE(%s)\n", vcd_trace_file_name);
		opentrace(vcd_trace_file_name);
	}

	void	close(void) {
		// TESTB<BASECLASS>::closetrace();
		m_done = true;
	}

	void	test_input(bool test_data) {
		m_test = test_data;
		m_core->i_test = (m_test) ? 1:0;
	}

	void	tick(void) {
		if (m_done)
			return;

		/*
		// Measure how fast we are actually sending frames
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

		m_vga((m_core->o_vga_vsync)?1:0, (m_core->o_vga_hsync)?1:0,
			m_core->o_vga_red,
			m_core->o_vga_grn,
			m_core->o_vga_blu);

		TESTB<Vdemo>::tick();
	}

	bool	on_tick(void) {
		for(int i=0; i<5; i++)
			tick();
		return true;
	}
};

TESTBENCH	*tb;

void	usage(void) {
	fprintf(stderr,
"Usage: main_tb [-tvh] [-g WIDTHxHEIGHT]\n"
"\n"
"\t-d <tracefile>vcd\tOpens a VCD file to contain a trace of all internal\n"
"\t\t\t\t(and external) signals\n"
"\t-g WIDTHxHEIGHT\tSets the simulated screen size to WIDTH by HEIGHT\n"
"\t\tpixels.\n"
"\t-h\tDisplays this usage message\n"
"\t-t\tTest mode: displays a set of color bars\n"
"\t-v\tVerbose\n");
}

void	usage_kill(void) {
	fprintf(stderr, "ERR: Invalid usage\n\n");
	usage();
	exit(EXIT_FAILURE);
}

int	main(int argc, char **argv) {
	Gtk::Main	main_instance(argc, argv);
	Verilated::commandArgs(argc, argv);
	bool	test_data = false, verbose_flag = false;;
	char	*ptr = NULL, *trace_file = NULL;
	int	hres = 1280, vres = 1024;

	int	opt;
	while((opt = getopt(argc, argv, "d:htg:")) != -1) {
		const char DELIMITERS[] = "x, ";
		switch(opt) {
		case 'd':
			if (verbose_flag)
				fprintf(stderr, "Opening trace file, %s\n", optarg);
			trace_file = strdup(optarg);
			break;
		case 'g': {

			ptr = strtok(optarg, DELIMITERS);
			if (!ptr)
				usage_kill();
			hres = atoi(ptr);
			ptr = strtok(NULL, DELIMITERS);
			if (!ptr)
				usage_kill();
			vres = atoi(ptr);

			VIDEOMODE vm(hres, vres);
			if (vm.err()) {
				fprintf(stderr, "Unsupported video mode, %dx%d\n", hres, vres);
				exit(EXIT_FAILURE);
			} else if (verbose_flag) {
				printf("Video mode set to %d x %d\n", hres, vres);
			}}
			break;
		case 'h':
			usage();
			exit(EXIT_SUCCESS);
			break;
		case 't':
			test_data = true;
			break;
		case 'v':
			verbose_flag = true;
		}
	}

	if ((hres != 1280)||(vres != 1024)) {
		fprintf(stderr, "WARNING: Memory mapped mode not supported for %d x %d, switching to test mode\n", hres, vres);
		test_data = true;
	}

	tb = new TESTBENCH(hres, vres);
	tb->test_input(test_data);
	tb->reset();

	if ((trace_file)&&(trace_file[0]))
		tb->opentrace(trace_file);
	Gtk::Main::run(tb->m_vga);

	exit(0);
}

