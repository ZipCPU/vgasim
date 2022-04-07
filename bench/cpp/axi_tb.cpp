////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axi_tb.cpp
// {{{
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	This is the main test bench class for the AXI-based demonstrator
//		that holds all the pieces together.  In this case, the test
//	bench consists of little more than a video simulator.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2017-2022, Gisselquist Technology, LLC
// {{{
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
// }}}
#include <signal.h>
#include <time.h>
#include <ctype.h>
#include <unistd.h>
#include <stdio.h>
#include <stdint.h>
#include <verilated_vcd_c.h>

#include "verilated.h"
#ifdef	HDMI
  #include "Vaxihdmi.h"
  #define	VCORE	Vaxihdmi
  #define	VMAIN	axihdmi
#else
  #include "Vaxidemo.h"
  #define	VCORE	Vaxidemo
  #define	VMAIN	axidemo
#endif


#define	TBASSERT(TB,A) do { if (!(A)) { (TB).closetrace(); } assert(A); } while(0);



#define	TRACECLASS	VerilatedVcdC
#include <verilated_vcd_c.h>
#include "tbclock.h"

template <class VA>	class AXITESTB {
public:
	VA		*m_core;
	bool		m_changed;
	TRACECLASS*	m_trace;
	bool		m_done, m_paused_trace;
	uint64_t	m_time_ps;
	// TBCLOCK is a clock support class, enabling multiclock simulation
	// operation.
	TBCLOCK		m_clk;
	TBCLOCK		m_pixclk;

	AXITESTB(void) {
		m_core = new VA;
		m_time_ps  = 0ul;
		m_trace    = NULL;
		m_done     = false;
		m_paused_trace = false;
		Verilated::traceEverOn(true);
// Set the initial clock periods
		m_clk.init(12500);	//   80.00 MHz
		m_pixclk.init(9260);	//  107.96 MHz
	}
	virtual ~AXITESTB(void) {
		if (m_trace) m_trace->close();
		delete m_core;
		m_core = NULL;
	}

	//
	// opentrace()
	// {{{
	// Useful for beginning a (VCD) trace.  To open such a trace, just call
	// opentrace() with the name of the VCD file you'd like to trace
	// everything into
	virtual	void	opentrace(const char *vcdname, int depth=99) {
		if (!m_trace) {
			m_trace = new TRACECLASS;
			m_core->trace(m_trace, 99);
			m_trace->spTrace()->set_time_resolution("ps");
			m_trace->spTrace()->set_time_unit("ps");
			m_trace->open(vcdname);
			m_paused_trace = false;
		}
	}
	// }}}

	//
	// trace()
	// {{{
	// A synonym for opentrace() above.
	//
	void	trace(const char *vcdname) {
		opentrace(vcdname);
	}
	// }}}

	//
	// pausetrace(pause)
	// {{{
	// Set/clear a flag telling us whether or not to write to the VCD trace
	// file.  The default is to write to the file, but this can be changed
	// by calling pausetrace.  pausetrace(false) will resume tracing,
	// whereas pausetrace(true) will stop all calls to Verilator's trace()
	// function
	//
	virtual	bool	pausetrace(bool pausetrace) {
		m_paused_trace = pausetrace;
		return m_paused_trace;
	}
	// }}}

	//
	// pausetrace()
	// {{{
	// Like pausetrace(bool) above, except that pausetrace() will return
	// the current status of the pausetrace flag above.  Specifically, it
	// will return true if the trace has been paused or false otherwise.
	virtual	bool	pausetrace(void) {
		return m_paused_trace;
	}
	// }}}

	//
	// closetrace()
	// {{{
	// Closes the open trace file.  No more information will be written
	// to it
	virtual	void	closetrace(void) {
		if (m_trace) {
			m_trace->close();
			delete m_trace;
			m_trace = NULL;
		}
	}
	// }}}

	//
	// eval()
	// {{{
	// This is a synonym for Verilator's eval() function.  It evaluates all
	// of the logic within the design.  AutoFPGA based designs shouldn't
	// need to be calling this, they should call tick() instead.  However,
	// in the off chance that your design inputs depend upon combinatorial
	// expressions that would be output based upon other input expressions,
	// you might need to call this function.
	virtual	void	eval(void) {
		m_core->eval();
	}
	// }}}

	//
	// tick()
	// {{{
	// tick() is the main entry point into this helper core.  In general,
	// tick() will advance the clock by one clock tick.  In a multiple clock
	// design, this will advance the clocks up until the nearest clock
	// transition.
	virtual	void	tick(void) {
		unsigned	mintime = m_clk.time_to_edge();

		if (m_pixclk.time_to_edge() < mintime)
			mintime = m_pixclk.time_to_edge();

		assert(mintime > 1);

		// Pre-evaluate, to give verilator a chance to settle any
		// combinatorial logic thatthat may have changed since the
		// last clockevaluation, and then record that in the trace.
		eval();
		if (m_trace && !m_paused_trace) m_trace->dump(m_time_ps+1);

		// Advance each clock
		m_core->i_clk = m_clk.advance(mintime);
		m_core->i_pixclk = m_pixclk.advance(mintime);

		m_time_ps += mintime;
		eval();
		// If we are keeping a trace, dump the current state to that
		// trace now
		if (m_trace && !m_paused_trace) {
			m_trace->dump(m_time_ps);
			m_trace->flush();
		}

		if (m_clk.falling_edge()) {
			m_changed = true;
			sim_clk_tick();
		}
		if (m_pixclk.falling_edge()) {
			m_changed = true;
			sim_pixclk_tick();
		}
	}
	// }}}

	virtual	void	sim_clk_tick(void) {
		// {{{
		// AutoFPGA will override this method within main_tb.cpp if any
		// @SIM.TICK key is present within a design component also
		// containing a @SIM.CLOCK key identifying this clock.  That
		// component must also set m_changed to true.
		m_changed = false;
	}
	// }}}
	virtual	void	sim_pixclk_tick(void) {
		// {{{
		// AutoFPGA will override this method within main_tb.cpp if any
		// @SIM.TICK key is present within a design component also
		// containing a @SIM.CLOCK key identifying this clock.  That
		// component must also set m_changed to true.
		m_changed = false;
	}
	// }}}
	virtual bool	done(void) {
		// {{{
		if (m_done)
			return true;

		if (Verilated::gotFinish())
			m_done = true;

		return m_done;
	}
	// }}}

	//
	// reset()
	// {{{
	// Sets the i_reset input for one clock tick.  It's really just a
	// function for the capabilies shown below.  You'll want to reset any
	// external input values before calling this though.
	virtual	void	reset(void) {
		m_core->i_reset = 1;
		tick();
		m_core->i_reset = 0;
		// printf("RESET\n");
	}
	// }}}
};

#ifdef	HDMI
#include "hdmisim.h"
#else
#include "vgasim.h"
#endif

#ifdef	ROOT_VERILATOR
#ifdef	HDMI
  #include "Vaxihdmi___024root.h"
#else
  #include "Vaxidemo___024root.h"
#endif

#define	VVAR(A)	VMAIN ## __DOT_ ## A
#elif defined(NEW_VERILATOR)
#define	VVAR(A)	busmaster__DOT_ ## A
#else
#define	VVAR(A)	v__DOT_ ## A
#endif


// No particular "parameters" need definition or redefinition here.
class	TESTBENCH : public AXITESTB<VCORE> {
	// Variable declarations
	// {{{
private:
	unsigned long	m_tx_busy_count;
	bool		m_done, m_test;
	int		m_state;
public:
#ifdef	HDMI
	HDMIWIN		m_win;
#else
	VGAWIN		m_win;
#endif
private:
	// }}}
	void	init(void) {
		// {{{
		m_core->i_reset = 1;
		m_state = 0;
		//
		m_done = false;

		Glib::signal_idle().connect(sigc::mem_fun((*this),&TESTBENCH::on_tick));
	}
	// }}}
public:

	TESTBENCH(void) : m_win(1280, 1024) {
		// {{{
		init();
	}
	// }}}

	TESTBENCH(int hres, int vres) : m_test(false), m_win(hres, vres) {
		// {{{
		init();
	}
	// }}}

	void	trace(const char *vcd_trace_file_name) {
		// {{{
		fprintf(stderr, "Opening TRACE(%s)\n", vcd_trace_file_name);
		opentrace(vcd_trace_file_name);
	}
	// }}}

	void	close(void) {
		// {{{
		// TESTB<BASECLASS>::closetrace();
		m_done = true;
	}
	// }}}

	void	tick(void) {
		// {{{
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

		AXITESTB<VCORE>::tick();
	}
	// }}}

	void	issue_write(unsigned addr, unsigned val) {
		// {{{
		m_core->S_AXI_AWVALID = 1;
		m_core->S_AXI_AWADDR  = addr & (unsigned)(-3);
		m_core->S_AXI_WVALID = 1;
		m_core->S_AXI_WDATA  = val;
		m_core->S_AXI_WSTRB  = 0x0f;
		m_core->S_AXI_BREADY = 1;
	}
	// }}}

	virtual	void	sim_clk_tick(void) {
		// {{{
		if (m_core->S_AXI_AWREADY)
			m_core->S_AXI_AWVALID = 0;
		if (m_core->S_AXI_WREADY)
			m_core->S_AXI_WVALID = 0;
		if (m_core->S_AXI_ARREADY)
			m_core->S_AXI_ARVALID = 0;

		switch(m_state) {
		case 0: case 1: case 2: case 3: case 4: case 5: case 6:
			m_core->i_reset = 1;
			m_core->S_AXI_AWVALID = 0;
			m_core->S_AXI_WVALID  = 0;
			m_core->S_AXI_ARVALID = 0;
			m_state++;
			break;
		case 7: case 8:
			m_core->i_reset = 0;
			m_state++;
			break;
		case 9:
			issue_write(0, 0); // Deactivate everything
			m_state++;
			break;
		case 10: if (m_core->S_AXI_BVALID) {
			issue_write(0x20, (m_win.height() << 16) | m_win.width());
			m_state++;
			} break;
		case 11: if (m_core->S_AXI_BVALID) {
			issue_write(0x24, (m_win.vporch()<<16) |m_win.hporch());
			m_state++;
			} break;
		case 12: if (m_core->S_AXI_BVALID) {
			issue_write(0x28, (m_win.vsync()<<16) |m_win.hsync());
			m_state++;
			} break;
		case 13: if (m_core->S_AXI_BVALID) {
			issue_write(0x2c, (m_win.raw_height()<<16) |m_win.raw_width());
			m_state++;
			} break;
		case 14: if (m_core->S_AXI_BVALID) {
			// issue_write(0x0c, 3);	// 4b clr, needs clrmap
			issue_write(0x0c, 5);	// 8b color
			m_state++;
			} break;
		case 15: if (m_core->S_AXI_BVALID) {
			issue_write(0x00, 5);
			m_state++;
			} break;
		//
		// Colormap: (RRGGBB)
		// ---------------------
		// 0x000000	0xaaaaaa
		// 0x800000	0xff0000
		// 0x008000	0x00ff00
		// 0x808000	0xffff00
		// 0x000080	0x0000ff
		// 0x800080	0xff00ff
		// 0x008080	0x00ffff
		// 0x555555	0xffffff
		//
		case 16: if (m_core->S_AXI_BVALID) {
			issue_write(0x400, 0x000000);
			m_state++;
			} break;
		case 17: if (m_core->S_AXI_BVALID) {
			issue_write(0x404, 0x800000);
			m_state++;
			} break;
		case 18: if (m_core->S_AXI_BVALID) {
			issue_write(0x408, 0x008000);
			m_state++;
			} break;
		case 19: if (m_core->S_AXI_BVALID) {
			issue_write(0x40c, 0x808000);
			m_state++;
			} break;
		case 20: if (m_core->S_AXI_BVALID) {
			issue_write(0x410, 0x000080);
			m_state++;
			} break;
		case 21: if (m_core->S_AXI_BVALID) {
			issue_write(0x414, 0x800080);
			m_state++;
			} break;
		case 22: if (m_core->S_AXI_BVALID) {
			issue_write(0x418, 0x008080);
			m_state++;
			} break;
		case 23: if (m_core->S_AXI_BVALID) {
			issue_write(0x41c, 0x555555);
			m_state++;
			} break;
		case 24: if (m_core->S_AXI_BVALID) {
			issue_write(0x420, 0xaaaaaa);
			m_state++;
			} break;
		case 25: if (m_core->S_AXI_BVALID) {
			issue_write(0x424, 0xff0000);
			m_state++;
			} break;
		case 26: if (m_core->S_AXI_BVALID) {
			issue_write(0x428, 0x00ff00);
			m_state++;
			} break;
		case 27: if (m_core->S_AXI_BVALID) {
			issue_write(0x42c, 0xffff00);
			m_state++;
			} break;
		case 28: if (m_core->S_AXI_BVALID) {
			issue_write(0x430, 0x0000ff);
			m_state++;
			} break;
		case 29: if (m_core->S_AXI_BVALID) {
			issue_write(0x434, 0xff00ff);
			m_state++;
			} break;
		case 30: if (m_core->S_AXI_BVALID) {
			issue_write(0x438, 0x00ff00);
			m_state++;
			} break;
		case 31: if (m_core->S_AXI_BVALID) {
			issue_write(0x43c, 0xffffff);
			m_state++;
			} break;
		default:
			if (m_core->S_AXI_BVALID) {
				printf("INIT SEQUENCE COMPLETE\n");
			}
			m_changed = false;
		} m_changed = true;
	}
	// }}}

	virtual	void	sim_pixclk_tick(void) {
		// {{{
#ifdef	HDMI
		m_win(m_core->o_hdmi_blu,
			m_core->o_hdmi_grn,
			m_core->o_hdmi_red);
#else
		m_win((m_core->o_vga_vsync)?1:0, (m_core->o_vga_hsync)?1:0,
			m_core->o_vga_red,
			m_core->o_vga_grn,
			m_core->o_vga_blu);
#endif
	}
	// }}}

	bool	on_tick(void) {
		// {{{
		for(int i=0; i<5; i++)
			tick();
		return true;
	}
	// }}}
};

TESTBENCH	*tb;

void	usage(void) {
	fprintf(stderr,
"Usage: axi_tb [-tvh]\n"
"\n"
"\t-d <tracefile>vcd\tOpens a VCD file to contain a trace of all internal\n"
"\t\t\t\t(and external) signals\n"
"\t-h\tDisplays this usage message\n"
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
	bool	verbose_flag = false;;
	char	*trace_file = NULL;
	const	int	hres = 1280, vres = 1024;

	int	opt;
	while((opt = getopt(argc, argv, "d:h")) != -1) {
		switch(opt) {
		case 'd':
			if (verbose_flag)
				fprintf(stderr, "Opening trace file, %s\n", optarg);
			trace_file = strdup(optarg);
			break;
		case 'h':
			usage();
			exit(EXIT_SUCCESS);
			break;
		case 'v':
			verbose_flag = true;
		}
	}

	tb = new TESTBENCH(hres, vres);
	tb->reset();

	if ((trace_file)&&(trace_file[0]))
		tb->opentrace(trace_file);
	Gtk::Main::run(tb->m_win);

	exit(0);
}

