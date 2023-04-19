################################################################################
##
## Filename:	bench/cpp/Makefile
## {{{
## Project:	vgasim, a Verilator based VGA simulator demonstration
##
## Purpose:	To direct the Verilator build of the VGA simulation sources.
##
## Targets:
##
##	main_tb
##		This demo program shows the utility of the VGA simulator, by
##		using the VGA outputs of a Verilator based test bench to drive
##		a window on your screen.
##
##	simcheck
##		This demo doesn't use verilator at all, but rather feeds the
##		result of the VGASOURCE directly into the VGASIM, providing
##		some confidence that both VGASOURCE and VGASIM components are
##		working.
##
##	axi_tb
##		An AXI demonstrator.  This demo configures an AXI Video source,
##		and then feeds the result into the VGA (or HDMI) simulator.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2017-2023, Gisselquist Technology, LLC
## {{{
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
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
## }}}
.PHONY: all
# Make certain the "all" target is the first and therefore the default target
all:
CXX	:= g++
OBJDIR	:= obj-pc
RTLD	:= ../rtl
YYMMDD  := `date +%Y%m%d`
VOBJDR	:= $(RTLD)/obj_dir
ifneq ($(VERILATOR_ROOT),)
VERILATOR:=$(VERILATOR_ROOT)/bin/verilator
else
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT | head -1 | sed -e " s/^.*=\s*//"')
endif
export	$(VERILATOR)
VROOT	:= $(VERILATOR_ROOT)
VINCD   := $(VROOT)/include
VINC	:= -I$(VINCD) -I$(VINCD)/vltstd -I$(VOBJDR)
INCS	:= -I$(RTLD)/obj_dir/ -I$(RTLD) -I$(VINCD)
VDEFS   := $(shell ./vversion.sh)
FLAGS	:= -Wall -Og -g $(VDEFS) -faligned-new
GFXFLAGS:= $(FLAGS) `pkg-config gtkmm-3.0 --cflags`
GFXLIBS := `pkg-config gtkmm-3.0 --libs`
CFLAGS  :=  $(GFXFLAGS)
SIMSOURCES:= vgasim.cpp hdmisim.cpp
SIMOBJECTS:= $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(SIMSOURCES)))
SIMHEADERS:= $(foreach header,$(subst .cpp,.h,$(SIMSOURCES)),$(wildcard $(header)))
VOBJS   := $(OBJDIR)/verilated.o $(OBJDIR)/verilated_vcd_c.o $(OBJDIR)/verilated_threads.o
all:	main_tb

SOURCES := main_tb.cpp vgasim.cpp vgasource.cpp hdmisim.cpp
HEADERS := image.h testb.h vgasim.h vgasource.h hdmisim.h videomode.h image.cpp
#
PROGRAMS := main_tb simcheck axi_tb hdmi_tb
# Now the return to the "all" target, and fill in some details
all:	$(PROGRAMS)

%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(VINCD)/%.cpp
	$(mk-objdir)
	$(CXX) $(FLAGS) $(INCS) -c $< -o $@

$(OBJDIR)/hdmi_tb.o: axi_tb.cpp
	$(mk-objdir)
	$(CXX) -DHDMI $(CFLAGS) $(INCS) -c $^ -o $@

simcheck: $(OBJDIR)/simcheck.o $(OBJDIR)/vgasim.o $(OBJDIR)/vgasource.o
	$(CXX) $(GFXFLAGS) $^ $(GFXLIBS) -lpthread -o $@

MAINOBJS := $(OBJDIR)/main_tb.o
main_tb: $(MAINOBJS) $(SIMOBJECTS) $(VOBJS) $(VOBJDR)/Vdemo__ALL.a
	$(CXX) $(GFXFLAGS) $^ $(VOBJDR)/Vdemo__ALL.a $(GFXLIBS) -lpthread -o $@

AXIOBJS := $(OBJDIR)/axi_tb.o
axi_tb: $(AXIOBJS) $(SIMOBJECTS) $(VOBJS) $(VOBJDR)/Vaxidemo__ALL.a
	$(CXX) $(GFXFLAGS) $^ $(VOBJDR)/Vaxidemo__ALL.a $(GFXLIBS) -lpthread -o $@

HDMIOBJS := $(OBJDIR)/hdmi_tb.o
hdmi_tb: $(HDMIOBJS) $(SIMOBJECTS) $(VOBJS) $(VOBJDR)/Vaxihdmi__ALL.a
	$(CXX) $(GFXFLAGS) $^ $(VOBJDR)/Vaxidemo__ALL.a $(GFXLIBS) -lpthread -o $@

.PHONY: clean
clean:
	rm -f *.vcd
	rm -f $(PROGRAMS)
	rm -rf $(OBJDIR)/

#
# The "depends" target, to know what files things depend upon.  The depends
# file itself is kept in $(OBJDIR)/depends.txt
#
define build-depends
	$(mk-objdir)
	@echo "Building dependency file"
	@$(CXX) $(CFLAGS) $(INCS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

.PHONY: archive
archive:
	tar --transform s,^,$(YYMMDD)-bench-cpp/, -chjf $(YYMMDD)-bench-cpp.tjz Makefile *.cpp *.h

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: depends

#
define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef


#
# The "tags" target
#
tags:	$(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)


-include $(OBJDIR)/depends.txt
