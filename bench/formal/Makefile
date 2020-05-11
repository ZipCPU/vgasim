################################################################################
##
## Filename:	bench/formal/Makefile
##
## Project:	vgasim, a Verilator based VGA simulator demonstration
##
## Purpose:	To direct the formal verification of particular display
##		components contained within this repository.
##
## Targets:	The default target, all, tests all of the components within
##		this module.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2017-2020, Gisselquist Technology, LLC
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
TESTS := llvga imgfifo
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl

SMTBMC  := yosys-smtbmc
# SOLVER  := -s z3
SOLVER  := -s yices
# SOLVER  := -s boolector
BMCARGS := --presat $(SOLVER) --unroll
# BMCARGS := $(SOLVER) --unroll
# BMCARGS := $(SOLVER)
INDARGS := $(SOLVER) -i

LLVGA	 := llvga
IFIFO	 := imgfifo

MASTER   := fwb_master.v
# SLAVE  := $(RTL)/ex/fwb_slave.v

$(IFIFO).smt2: $(RTL)/$(IFIFO).v $(RTL)/atxfifo.v $(RTL)/transferstb.v
$(IFIFO).smt2: $(MASTER) $(IFIFO).ys
	yosys -ql $(IFIFO).yslog -s $(IFIFO).ys

.PHONY: $(LLVGA)
$(LLVGA) : $(LLVGA)/PASS
$(LLVGA)/PASS: $(LLVGA).sby ../../rtl/llvga.v ../../rtl/vgatestsrc.v
	sby -f $(LLVGA).sby

.PHONY: $(IFIFO)
$(IFIFO) : $(IFIFO)/PASS
$(IFIFO)/PASS: $(IFIFO).sby $(RTL)/imgfifo.v $(RTL)/transferstb.v
$(IFIFO)/PASS: $(RTL)/atxfifo.v $(MASTER)
	sby -f $(IFIFO).sby

.PHONY: clean
clean:
	rm -rf $(LLVGA)/ $(IFIFO)/
