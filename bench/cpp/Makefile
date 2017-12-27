.PHONY: all
# Make certain the "all" target is the first and therefore the default target
all:
CXX	:= g++
OBJDIR	:= obj-pc
RTLD	:= ../../rtl
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
FLAGS	:= -Wall -Og -g $(VDEFS)
GFXFLAGS:= $(GFXFLAGS) `pkg-config gtkmm-3.0 --cflags`
GFXLIBS := `pkg-config gtkmm-3.0 --libs`
CFLAGS  :=  $(GFXFLAGS)
SIMSOURCES:= vgasim.cpp
SIMOBJECTS:= $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(SIMSOURCES)))
SIMHEADERS:= $(foreach header,$(subst .cpp,.h,$(SIMSOURCES)),$(wildcard $(header)))
VOBJS   := $(OBJDIR)/verilated.o $(OBJDIR)/verilated_vcd_c.o
all:	main_tb archive

SOURCES := main_tb.cpp vgasim.cpp
HEADERS := image.h testb.h vgasim.h videomode.h image.cpp
#
PROGRAMS := main_tb
# Now the return to the "all" target, and fill in some details
all:	$(PROGRAMS)

%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(VINCD)/%.cpp
	$(mk-objdir)
	$(CXX) $(FLAGS) $(INCS) -c $< -o $@


MAINOBJS := $(OBJDIR)/main_tb.o
main_tb: $(MAINOBJS) $(SIMOBJECTS) $(VOBJS) $(VOBJDR)/Vwbvgaframe__ALL.a
	$(CXX) $(GFXFLAGS) $^ $(VOBJDR)/Vwbvgaframe__ALL.a $(GFXLIBS) -o $@

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
