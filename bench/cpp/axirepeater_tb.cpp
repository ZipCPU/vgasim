////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axirepeater_tb.cpp
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

#include <verilated.h>
// Verilator (stuffs)
#include "Vaxirepeater.h"

#define	TBASSERT(TB,A) do { if (!(A)) { (TB).closetrace(); } assert(A); } while(0);
#define	TRACECLASS	VerilatedVcdC
#include <verilated_vcd_c.h>

#include "tbclock.h"
// #include "testb.h"
// #include "twoc.h"

#include "hdmisim.h"
#include "hdmisource.h"

#ifdef	NEW_VERILATOR
#define	VVAR(A)	busmaster__DOT_ ## A
#else
#define	VVAR(A)	v__DOT_ ## A
#endif

const	int	WIDTH = 640, HEIGHT = 480;

// No particular "parameters" need definition or redefinition here.
class	TESTBENCH {
public:
	HDMIWIN		m_win;
	HDMISOURCE	m_src;
	Vaxirepeater	*m_core;
	TRACECLASS	*m_trace;
	TBCLOCK		m_clk, m_pixclk;
	unsigned long	m_time_ps;
	bool		m_done, m_paused_trace;
	int		m_state;

	TESTBENCH(void) : m_win(WIDTH, HEIGHT), m_src(WIDTH, HEIGHT)
			// m_vga(1280, 1024)
			// m_vga(1280,720)
			{
		m_core = new Vaxirepeater;
		Verilated::traceEverOn(true);
		m_time_ps = 0ul;
		m_trace = NULL;
		m_done = false;
		m_paused_trace = false;
		m_clk.init(12500);	//  80.00MHz
		// m_pixclk.init(9260);	// 107.96MHz
		m_pixclk.init(39968);	//  25.02MHz

		//
		Glib::signal_idle().connect(
				sigc::mem_fun((*this),&TESTBENCH::on_tick));
	}

	~TESTBENCH(void) {
		if (m_trace) m_trace->close();
		delete m_core;
		m_core = NULL;
	}

	//
	// opentrace()
	//
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
	//
	// trace()
	//
	// A synonym for opentrace() above.
	//
	void	trace(const char *vcdname) {
		opentrace(vcdname);
	}

	//
	// pausetrace(pause)
	//
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

	//
	// pausetrace()
	//
	// Like pausetrace(bool) above, except that pausetrace() will return
	// the current status of the pausetrace flag above.  Specifically, it
	// will return true if the trace has been paused or false otherwise.
	virtual	bool	pausetrace(void) {
		return m_paused_trace;
	}

	//
	// closetrace()
	//
	// Closes the open trace file.  No more information will be written
	// to it
	virtual	void	closetrace(void) {
		if (m_trace) {
			m_trace->close();
			delete m_trace;
			m_trace = NULL;
		}
	}

	//
	// eval()
	//
	// This is a synonym for Verilator's eval() function.  It evaluates all
	// of the logic within the design.  AutoFPGA based designs shouldn't
	// need to be calling this, they should call tick() instead.  However,
	// in the off chance that your design inputs depend upon combinatorial
	// expressions that would be output based upon other input expressions,
	// you might need to call this function.
	virtual	void	eval(void) {
		m_core->eval();
	}


	//
	// tick()
	//
	// tick() is the main entry point into this helper core.  In general,
	// tick() will advance the clock by one clock tick.  In a multiple clock
	// design, this will advance the clocks up until the nearest clock
	// transition.
	virtual	void	tick(void) {
		if (m_done)
			return;

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
		m_core->i_cam_clk  = m_pixclk.advance(mintime);
		m_core->i_hdmi_clk = m_core->i_cam_clk;

		m_time_ps += mintime;
		eval();
		// If we are keeping a trace, dump the current state to that
		// trace now
		if (m_trace && !m_paused_trace) {
			m_trace->dump(m_time_ps);
			m_trace->flush();
		}

		if (m_clk.falling_edge()) {
			sim_clk_tick();
		} if (m_pixclk.falling_edge()) {
			sim_pixclk_tick();
		}
	}

	void	issue_write(unsigned addr, unsigned val) {
		m_core->S_AXI_AWVALID = 1;
		m_core->S_AXI_AWADDR  = addr & (unsigned)(-3);
		m_core->S_AXI_WVALID = 1;
		m_core->S_AXI_WDATA  = val;
		m_core->S_AXI_WSTRB  = 0x0f;
		m_core->S_AXI_BREADY = 1;
	}

	void	issue_read(unsigned addr) {
		m_core->S_AXI_AWVALID = 0;
		m_core->S_AXI_WVALID  = 0;
		m_core->S_AXI_WDATA   = 0;
		m_core->S_AXI_WSTRB   = 0;
		m_core->S_AXI_ARVALID = 1;
		m_core->S_AXI_BREADY  = 0;
		m_core->S_AXI_ARADDR  = addr & (unsigned)(-3);
		m_core->S_AXI_RREADY  = 1;
	}

#define	R_RECORD	0
#define	R_RECDMA	(R_RECORD +  0)	// DMA
#define	R_RECFRAMEINFO	(R_RECORD +  4)	// DMA
#define	R_RECBASE	(R_RECORD +  8)	// DMA
#define	R_RECBASE_HI	(R_RECORD + 12)	// DMA
#define	R_RECCLOCK	(R_RECORD + 16)	// PIXEL FREQUENCY
#define	R_RECPIX2BIN	(R_RECORD + 20)	// PIXEL MAPPING, LOCK STATUS
#define	R_RECFRAMERATE	(R_RECORD + 28)	// FRAME RATE
#define	R_RECSIZE	(R_RECORD + 32)	// IMSIZE
#define	R_RECPORCH	(R_RECORD + 36)	// PORCH
#define	R_RECSYNC	(R_RECORD + 40)	// SYNC
#define	R_RECRAW	(R_RECORD + 44) // RAW
// #define	R_RECCKPFRAME	(R_RECORD + 48)

#define	R_DISPLAY	0x0800
#define	R_VIDCONTROL	(R_DISPLAY+   0)
#define	R_VIDBASE	(R_DISPLAY+   8)
#define	R_VIDPSIZE	(R_DISPLAY+  12)
#define	R_VIDCLOCK	(R_DISPLAY+  16)
#define	R_VIDSIZE	(R_DISPLAY+  32)
#define	R_VIDPORCH	(R_DISPLAY+  36)
#define	R_VIDSYNC	(R_DISPLAY+  40)
#define	R_VIDRAW	(R_DISPLAY+  44)
#define	R_VIDCMAP	(R_DISPLAY+0x0400)

	virtual	void	sim_clk_tick(void) {
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
			issue_write(R_DISPLAY, 0); // Deactivate everything
			m_state++;
			break;
		case 10: if (m_core->S_AXI_BVALID) {
			issue_write(R_VIDSIZE, (m_win.height() << 16) | m_win.width());
			m_state++;
			} break;
		case 11: if (m_core->S_AXI_BVALID) {
			issue_write(R_VIDPORCH, (m_win.vporch()<<16) |m_win.hporch());
			m_state++;
			} break;
		case 12: if (m_core->S_AXI_BVALID) {
			issue_write(R_VIDSYNC, (m_win.vsync()<<16) |m_win.hsync());
			m_state++;
			} break;
		case 13: if (m_core->S_AXI_BVALID) {
			issue_write(R_VIDRAW, (m_win.raw_height()<<16) |m_win.raw_width());
			m_state++;
			} break;
		case 14: if (m_core->S_AXI_BVALID) {
			issue_write(R_VIDBASE, 0);
			m_state++;
			} break;
		case 15: if (m_core->S_AXI_BVALID) {
			issue_write(R_VIDPSIZE, 0x7);	// 32b color
			m_state++;
			} break;
		case 16: if (m_core->S_AXI_BVALID) {
			issue_write(R_VIDCONTROL, 13);	// Activate the display
			m_state++;
			} break;
		case 17: if (m_core->S_AXI_BVALID) {
			issue_write(R_RECORD, 0); // Make sure cam dma is off
			m_state++;
			} break;
		case 18: if (m_core->S_AXI_BVALID) {
			issue_write(R_RECPIX2BIN, 3); // Pixel record type
			m_state++;
			} break;
		case 19: if (m_core->S_AXI_BVALID) {
			issue_write(R_RECFRAMEINFO, (m_win.height() << 16) | (m_win.width() * 4)); //NLINEs,BYTS/LN
			m_state++;
			} break;
		case 20: if (m_core->S_AXI_BVALID) {
			printf("Waiting for lock\n");
			issue_read(R_RECPIX2BIN); // Check if we are locked
			m_state++;
			} break;
		case 21: if (m_core->S_AXI_RVALID) {
			if (m_core->S_AXI_RDATA & 0x80000000) {
				// We are locked,we can now start recording
				printf("Locked!  Starting to record\n");
				issue_write(R_RECORD, 15);
				m_state++;
			} else
				// Keep checking
				issue_read(R_RECPIX2BIN); // Locked yet?
			} break;
		default:
			if (m_core->S_AXI_BVALID) {
				printf("INIT SEQUENCE COMPLETE\n");
			}
		}
	}

	virtual	void	sim_pixclk_tick(void) {
		int	red, green, blue;

		m_src(blue, green, red);
		m_core->i_cam_blu = blue;
		m_core->i_cam_grn = green;
		m_core->i_cam_red = red;
		m_win(m_core->o_hdmi_blu, m_core->o_hdmi_grn, m_core->o_hdmi_red);
	}

	virtual bool	done(void) {
		if (m_done)
			return true;

		if (Verilated::gotFinish())
			m_done = true;

		return m_done;
	}

	//
	// reset()
	//
	// Sets the i_reset input for one clock tick.  It's really just a
	// function for the capabilies shown below.  You'll want to reset any
	// external input values before calling this though.
	virtual	void	reset(void) {
		m_core->i_reset = 1;
		tick();
		m_core->i_reset = 0;
		// printf("RESET\n");
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

	// tb->opentrace("repeater.vcd");
	Gtk::Main::run(tb->m_win);

	exit(0);
}

