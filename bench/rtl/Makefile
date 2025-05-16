################################################################################
##
## Filename:	bench/rtl/Makefile
## {{{
## Project:	vgasim, a Verilator based VGA simulator demonstration
##
## Purpose:	To direct the Verilator build of the VGA simulation sources.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2017-2025, Gisselquist Technology, LLC
## {{{
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of the GNU General Public License as published
## by the Free Software Foundation, either version 3 of the License, or (at
## your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
## }}}
all:	test
FBDIR := .
VDIRFB:= $(FBDIR)/obj_dir
RTL   := ../../rtl
DEMOS := demo axidemo axihdmi axirepeater spritedemo histdemo tracedemo
.PHONY: $(DEMOS)

.DELETE_ON_ERROR:

test: demo axidemo axihdmi axirepeater spritedemo histdemo tracedemo
demo:        $(VDIRFB)/Vdemo__ALL.a
axidemo:     $(VDIRFB)/Vaxidemo__ALL.a
axihdmi:     $(VDIRFB)/Vaxihdmi__ALL.a
axirepeater: $(VDIRFB)/Vaxirepeater__ALL.a
spritedemo:  $(VDIRFB)/Vspritedemo__ALL.a
histdemo:    $(VDIRFB)/Vhistdemo__ALL.a
tracedemo:   $(VDIRFB)/Vtracedemo__ALL.a

VOBJ := obj_dir
SUBMAKE := $(MAKE) --no-print-directory --directory=$(VOBJ) -f
ifeq ($(VERILATOR_ROOT),)
VERILATOR := verilator
else
VERILATOR := $(VERILATOR_ROOT)/bin/verilator
endif
VFLAGS := -Wall --MMD -O3 --trace -y ../../rtl -cc

## Generic rules
## {{{
# $(VDIRFB)/V%.cpp $(VDIRFB)/V%.h $(VDIRFB)/V%.mk: $(FBDIR)/%.v
$(VDIRFB)/V%.h:  $(VDIRFB)/V%.cpp
$(VDIRFB)/V%.cpp: $(VDIRFB)/V%.mk
$(VDIRFB)/V%.mk: $(FBDIR)/%.v
	$(VERILATOR) $(VFLAGS) $*.v

$(VDIRFB)/V%__ALL.a: $(VDIRFB)/V%.mk
	$(SUBMAKE) V$*.mk
## }}}

## Vdemo
## {{{
# $(VDIRFB)/Vdemo.h: $(VDIRFB)/Vdemo.h
# $(VDIRFB)/Vdemo.mk: $(VDIRFB)/Vdemo.cpp
$(VDIRFB)/Vdemo__ALL.a: $(VDIRFB)/Vdemo.mk
$(VDIRFB)/Vdemo.h: demo.v
## }}}

## axidemo
## {{{
$(VDIRFB)/Vaxidemo__ALL.a: $(VDIRFB)/Vaxidemo.h
$(VDIRFB)/Vaxidemo__ALL.a: $(VDIRFB)/Vaxidemo.cpp
$(VDIRFB)/Vaxidemo__ALL.a: $(VDIRFB)/Vaxidemo.mk
$(VDIRFB)/Vaxidemo.h: axidemo.v

$(VDIRFB)/Vaxidemo.cpp $(VDIRFB)/Vaxidemo.mk: axidemo.v demofull.v $(RTL)/axivdisplay.v
	$(VERILATOR) $(VFLAGS) -y $(RTL)/ -y $(RTL)/hdmi -cc axidemo.v

## }}}

## axihdmi
## {{{
$(VDIRFB)/Vaxihdmi.cpp $(VDIRFB)/Vaxihdmi.mk: axidemo.v demofull.v $(RTL)/axivdisplay.v $(RTL)/axishdmi.v
	$(VERILATOR) $(VFLAGS) -DHDMI -y $(RTL)/ -y $(RTL)/hdmi --prefix Vaxihdmi -cc axidemo.v
## }}}

## axirepeater
## {{{
$(VDIRFB)/Vaxirepeater.cpp $(VDIRFB)/Vaxirepeater.mk: axirepeater.v demofull.v $(RTL)/axivcamera.v $(RTL)/hdmi2vga.v
	$(VERILATOR) $(VFLAGS) -DHDMI -y $(RTL)/ -y $(RTL)/hdmi -cc axirepeater.v
## }}}

## spritedemo
## {{{
$(VDIRFB)/Vspritedemo.cpp $(VDIRFB)/Vspritedemo.mk: spritedemo.v demofull.v $(RTL)/axivcamera.v $(RTL)/hdmi2vga.v
	$(VERILATOR) $(VFLAGS) -DHDMI -y $(RTL)/ -y $(RTL)/hdmi -cc spritedemo.v
## }}}

## histdemo
## {{{
$(VDIRFB)/Vhistdemo.cpp $(VDIRFB)/Vhistdemo.mk: histdemo.v sintable.v $(RTL)/axishdmi.v $(RTL)/sfifo.v $(RTL)/gfx/vid_histogram.v $(RTL)/hdmi/tmdsencode.v
	$(VERILATOR) $(VFLAGS) -y $(RTL)/ -y $(RTL)/gfx -y $(RTL)/hdmi -cc histdemo.v
## }}}

## tracedemo
## {{{
$(VDIRFB)/Vtracedemo.cpp $(VDIRFB)/Vtracedemo.mk: tracedemo.v sintable.v $(RTL)/axishdmi.v $(RTL)/sfifo.v $(RTL)/gfx/vid_trace.v $(RTL)/hdmi/tmdsencode.v
	$(VERILATOR) $(VFLAGS) -y $(RTL)/ -y $(RTL)/gfx -y $(RTL)/hdmi -cc tracedemo.v
## }}}

## CLEAN
## {{{
.PHONY: clean
clean:
	rm -rf $(VDIRFB)/
## }}}

# DEPENDS
## {{{
# Note Verilator's dependency created information, and include it here if we
# can
DEPS := $(wildcard $(VDIRFB)/*.d)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(DEPS),)
include $(DEPS)
endif
endif
## }}}
