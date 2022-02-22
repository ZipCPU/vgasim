################################################################################
##
## Filename:	bench/formal/Makefile
## {{{
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
## }}}
## Copyright (C) 2017-2022, Gisselquist Technology, LLC
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
all:
## }}}
GFX := vid_waterfall_r vid_waterfall_w vid_histogram
TESTS := llvga axissprite axishdmi pix2stream atxfifo vidstream2pix $(GFX) # imgfifo
all: $(TESTS)

## Definitions
## {{{
RTL := ../../rtl

ATXFIFO	 := atxfifo
LLVGA	 := llvga
IFIFO	 := imgfifo
SPRITE	 := axissprite
AXISHDMI := axishdmi
PIX2STREAM := pix2stream
VID2PIX  := vidstream2pix
WFALLW   := vid_waterfall_w
WFALLR   := vid_waterfall_r
HSGRAM   := vid_histogram

MASTER   := fwb_master.v
# SLAVE  := $(RTL)/ex/fwb_slave.v
## }}}

.PHONY: $(ATXFIFO)
## {{{
$(ATXFIFO) : $(ATXFIFO)_prf/PASS
$(ATXFIFO)_prf/PASS: $(ATXFIFO).sby $(RTL)/$(ATXFIFO).v
	sby -f $(ATXFIFO).sby prf
## }}}

.PHONY: $(LLVGA)
## {{{
$(LLVGA) : $(LLVGA)_prf/PASS
$(LLVGA)_prf/PASS: $(LLVGA).sby $(RTL)/llvga.v $(RTL)/vgatestsrc.v
	sby -f $(LLVGA).sby prf
## }}}

.PHONY: $(IFIFO)
## {{{
$(IFIFO) : $(IFIFO)/PASS
$(IFIFO)/PASS: $(IFIFO).sby $(RTL)/imgfifo.v $(RTL)/transferstb.v
$(IFIFO)/PASS: $(RTL)/atxfifo.v $(MASTER)
	sby -f $(IFIFO).sby
## }}}

.PHONY: $(SPRITE)
## {{{
$(SPRITE) : $(SPRITE)_prf/PASS    $(SPRITE)_prfns/PASS
$(SPRITE) : $(SPRITE)_prfsof/PASS $(SPRITE)_prfsofns/PASS
$(SPRITE) : $(SPRITE)_cvr/PASS
$(SPRITE)_prf/PASS: $(SPRITE).sby $(RTL)/axissprite.v
	sby -f $(SPRITE).sby prf
$(SPRITE)_prfns/PASS: $(SPRITE).sby $(RTL)/axissprite.v
	sby -f $(SPRITE).sby prfns
$(SPRITE)_prfsof/PASS: $(SPRITE).sby $(RTL)/axissprite.v
	sby -f $(SPRITE).sby prfsof
$(SPRITE)_prfsofns/PASS: $(SPRITE).sby $(RTL)/axissprite.v
	sby -f $(SPRITE).sby prfsofns
$(SPRITE)_cvr/PASS: $(SPRITE).sby $(RTL)/axissprite.v
	sby -f $(SPRITE).sby cvr
## }}}

.PHONY: $(AXISHDMI)
## {{{
$(AXISHDMI) : $(AXISHDMI)_prf/PASS
$(AXISHDMI)_prf/PASS: $(AXISHDMI).sby $(RTL)/$(AXISHDMI).v
	sby -f $(AXISHDMI).sby prf
## }}}

.PHONY: $(PIX2STREAM)
## {{{
$(PIX2STREAM) : $(PIX2STREAM)_prf/PASS $(PIX2STREAM)_prf64/PASS $(PIX2STREAM)_cvr/PASS
$(PIX2STREAM)_prf/PASS: $(PIX2STREAM).sby $(RTL)/$(PIX2STREAM).v $(RTL)/skidbuffer.v
	sby -f $(PIX2STREAM).sby prf
$(PIX2STREAM)_prf64/PASS: $(PIX2STREAM).sby $(RTL)/$(PIX2STREAM).v $(RTL)/skidbuffer.v
	sby -f $(PIX2STREAM).sby prf64
$(PIX2STREAM)_cvr/PASS: $(PIX2STREAM).sby $(RTL)/$(PIX2STREAM).v $(RTL)/skidbuffer.v
	sby -f $(PIX2STREAM).sby cvr
## }}}

.PHONY: $(VID2PIX)
## {{{
$(VID2PIX): $(VID2PIX)_prf/PASS   $(VID2PIX)_prfsof/PASS
$(VID2PIX): $(VID2PIX)_prf64/PASS $(VID2PIX)_prf64sof/PASS
$(VID2PIX): $(VID2PIX)_cvr/PASS
$(VID2PIX)_prf/PASS: $(VID2PIX).sby $(RTL)/$(VID2PIX).v $(RTL)/skidbuffer.v
	sby -f $(VID2PIX).sby prf
$(VID2PIX)_prfsof/PASS: $(VID2PIX).sby $(RTL)/$(VID2PIX).v $(RTL)/skidbuffer.v
	sby -f $(VID2PIX).sby prfsof
$(VID2PIX)_prf64/PASS: $(VID2PIX).sby $(RTL)/$(VID2PIX).v $(RTL)/skidbuffer.v
	sby -f $(VID2PIX).sby prf64
$(VID2PIX)_prf64sof/PASS: $(VID2PIX).sby $(RTL)/$(VID2PIX).v $(RTL)/skidbuffer.v
	sby -f $(VID2PIX).sby prf64sof
$(VID2PIX)_cvr/PASS: $(VID2PIX).sby $(RTL)/$(VID2PIX).v $(RTL)/skidbuffer.v
	sby -f $(VID2PIX).sby cvr
## }}}

.PHONY: $(WFALLW) waterfall
## {{{
waterfall: $(WFALLW) $(WFALLR)
$(WFALLW): $(WFALLW)_prf/PASS
$(WFALLW)_prf/PASS: $(WFALLW).sby $(RTL)/gfx/$(WFALLW).v $(RTL)/sfifo.v faxivideo.v fwb_master.v
	sby -f $(WFALLW).sby prf
## }}}

.PHONY: $(WFALLR)
## {{{
$(WFALLR): $(WFALLR)_prf/PASS
$(WFALLR)_prf/PASS: $(WFALLR).sby $(RTL)/gfx/$(WFALLR).v $(RTL)/sfifo.v faxivideo.v fwb_master.v
	sby -f $(WFALLR).sby prf
## }}}

.PHONY: $(HSGRAM) histogram
## {{{
histogram: $(HSGRAM)
$(HSGRAM): $(HSGRAM)_prf/PASS
$(HSGRAM)_prf/PASS: $(HSGRAM).sby $(RTL)/gfx/$(HSGRAM).v faxivideo.v
	sby -f $(HSGRAM).sby prf
## }}}

.PHONY: clean
## {{{
clean:
	rm -rf $(LLVGA)/ $(IFIFO)/ $(SPRITE)_*/
	rm -rf $(AXISHDMI)_*/ $(PIX2STREAM)_*/
	rm -rf $(ATXFIFO)_*/
	rm -rf $(VID2PIX)_*/
	rm -rf $(WFALLW)_*/ $(WFALLR)_*/
	rm -rf $(HSGRAM)_*/
## }}}
