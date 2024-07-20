This directory contains a variety of video components.  These are designed
to be stream processing components, accepting AXI video stream inputs and
producing AXI video stream outputs.

1. [vid_clrmap](vid_clrmap.v) takes an 8b color pixel and produces three
   8b color outputs.  This component is entirely combinatorial.  This
   component is used to create the false color used by the
   [waterfall](vid_waterfall.v) component.

2. [vid_empty](vid_empty.v) generates a video output with a constant pixel.
   This coupled with one or more [overlays](../axisvoverlay.v) can be used
   to compose streams from components.

3. [vid_histogram](vid_histogram.v) takes an AXI stream input, and uses it to
   generate a plot of a histogram.

4. [vid_mux](vid_mux.v) takes multiple AXI video stream inputs, and selects
   one from among them.  The selection is allowed to change after the last
   pixel in a frame.  Unselected video streams are held by holding their
   various `READY` signals low.  Proper timing is provided by propagating
   the `READY` upstream from the display driver.

5. [vid_split](vid_split.v) takes an AXI stream of FFT data, and generates both
   a spectral display (via the [vid_trace](vid_trace.v) component) on the
   top of a video screen, and a waterfall display (via
   [vid_waterfall](vid_waterfall.v) on the bottom of the screen.  This depends
   upon the [overlay module](../axisvoverlay.v) to add the various components
   videos onto the AXI video stream.

6. [vid_trace](vid_trace.v) generates a trace from a time series of data.
   The time series arrives via AXI stream.

   This component is (currently) ripe for a redesign.  It does not include
   any units, nor does it have a good interface for adding units to the
   display.  A second potential problem is the challenge associated with
   displaying more data than can be visually viewed at any given time.  This
   component has no way (at present) of compressing data in time.

7. [vid_waterfall](vid_waterfall.v) takes an AXI stream of 8b grayscale inputs,
   and produces a (grayscale) waterfall display.  Data coming into the module
   is first written to memory, via [vid_waterfall_w](vid_waterfall_w.v).  A
   pointer is also produced by the [writer](vid_waterfall_w.v), which is then
   used as the start of the display.  This memory is then read in video
   time--much like a generic framebuffer--via
   [vid_waterfall_r](vid_waterfall_r.v) in order to generate the actual
   display.  Video scrolls vertically up over time.  The
   [vid_clrmap](vid_clrmap.v) component may be used to provide false color.

   As with the [vid_trace](vid_trace.v) component, this component does not (yet)
   have any ability to provide labels on its axes.


