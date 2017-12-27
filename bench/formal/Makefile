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
## Copyright (C) 2017, Gisselquist Technology, LLC
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
TESTS := llvga
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

MASTER := $(RTL)/aux/fwb_master.v
SLAVE  := $(RTL)/aux/fwb_slave.v

$(LLVGA).smt2: $(RTL)/$(LLVGA).v $(LLVGA).ys
	yosys -ql $(LLVGA).yslog -s $(LLVGA).ys

$(LLVGA) : $(LLVGA).check
$(LLVGA).check: $(LLVGA).smt2
	@rm -f $(LLVGA).check
	$(SMTBMC)    $(BMCARGS) -t 20 --dump-vcd $(LLVGA).vcd $(LLVGA).smt2
	$(SMTBMC)    $(INDARGS) -t 58 --dump-vcd $(LLVGA).vcd $(LLVGA).smt2
	$(SMTBMC) -g $(BMCARGS) -t 60 --dump-vcd $(LLVGA).vcd $(LLVGA).smt2
	touch $@

.PHONY: clean
clean:
	rm -f $(LLVGA).smt2   $(LLVGA)*.vcd   $(LLVGA).yslog
	rm -f *.check
