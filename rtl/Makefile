################################################################################
##
## Filename:	rtl/Makefile
##
## Project:	vgasim, a Verilator based VGA simulator demonstration
##
## Purpose:	To direct the Verilator build of the VGA simulation sources.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2017-2022, Gisselquist Technology, LLC
##
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of  the GNU General Public License as published
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
##
## License:	GPL, v3, as defined and found on www.gnu.org,
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
##
all:	test
FBDIR := .
VDIRFB:= $(FBDIR)/obj_dir

.PHONY: wbvgaframe
test: wbvgaframe
wbvgaframe: $(VDIRFB)/Vwbvgaframe__ALL.a

VOBJ := obj_dir
SUBMAKE := $(MAKE) --no-print-directory --directory=$(VOBJ) -f
ifeq ($(VERILATOR_ROOT),)
VERILATOR := verilator
else
VERILATOR := $(VERILATOR_ROOT)/bin/verilator
endif
VFLAGS := -Wall --MMD --trace -cc

$(VDIRFB)/Vwbvgaframe__ALL.a: $(VDIRFB)/Vwbvgaframe.h
$(VDIRFB)/Vwbvgaframe__ALL.a: $(VDIRFB)/Vwbvgaframe.cpp
$(VDIRFB)/Vwbvgaframe__ALL.a: $(VDIRFB)/Vwbvgaframe.mk
$(VDIRFB)/Vwbvgaframe.h: wbvgaframe.v

$(VDIRFB)/V%.cpp $(VDIRFB)/V%.h $(VDIRFB)/V%.mk: $(FBDIR)/%.v
	$(VERILATOR) $(VFLAGS) $*.v

$(VDIRFB)/V%__ALL.a: $(VDIRFB)/V%.mk
	$(SUBMAKE) V$*.mk

.PHONY: clean
clean:
	rm -rf $(VDIRFB)/

#
# Note Verilator's dependency created information, and include it here if we
# can
DEPS := $(wildcard $(VDIRFB)/*.d)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(DEPS),)
include $(DEPS)
endif
endif
