This directory contains several (close to) top level demonstrators.  First, it
contains two frame buffer demonstrators.  These read an image from memory and
display it in either VGA or HDMI.  They include [axivideo](axivideo.v),
based on the AXI stream and AXI4 memory protocol, and
[wbvgaframe](wbvgaframe.v) which does (roughly) the same thing based upon the
Wishbone protocol.  The second demonstrator is the [axicamera](axicamera.v)
demonstrator, which synchronizes to an incoming video signal, generates a
pixel stream, converts it to a stream of memory words, and then uses
the [axivcamera](axivcamera.v) video DMA to write this signal to memory.

This directory also contains several other valuable video components within it.

1. [afifo](afifo.v) is an asynchronous FIFO, modified to also produce an
   (estimate) of the fill within the FIFO so as to know when to start refilling
   it.

2. [axicamera.v](axicamera.v) is a camera demonstration, from AXI-lite
   configuration port, to VGA or HDMI reception, video synchronization,
   timing and frame size determination, all the way to AXI4 memory output.

3. [axishdmi.v](axishdmi.v) converts an incoming AXI stream to HDMI's ten bit
   words.  Does not include the OSERDES, as this may be different from one
   design to the next.

4. [axissprite.v](axissprite.v) takes an AXI video stream and produces a second
   AXI video stream as an output, this time with a sprite added onto that stream
   at a known location.  An AXI-lite interface allows you to write to the
   sprite memory and/or adjust its position on the generated video stream.

5. [axisvga.v](axisvga.v) converts an incoming AXI stream to a (digitized) VGA
   output.  Does not include any analog drivers necessary to properly convert
   the digitized pixels to VGA's analog reg, green, or blue wires.

6. [axisvoverlay.v](axisvoverlay.v) takes two incoming video streams--a primary
   and an overlay, and places the overlay stream on top of the primary.  Options
   are provided to adjust where the overlay will be placed on the primary's
   display.

7. [axivcamera.v](axivcamera.v) copies an incoming AXI video stream to a frame
   buffer in memory.  It's basically a video DMA.  It can copy continuously to
   the same area of memory, or copy a finite number of frames to memory.

8. [axivdisplay.v](axivdisplay.v) reads from a frame buffer in memory, using the
   AXI bus protocol, to create an AXI video stream.

9. [axivideo.v](axivideo.v) A full frame buffer example display using an
   AXI4 bus, internal AXI video stream, and generating either an outgoing HDMI
   or VGA data stream.

10. [clkcounter.v](clkcounter.v) calculates the speed of an incoming clock with
    respect to a system clock.  Can be used as part of an incoming video
    demonstrator, where the speed of the video clock needs to be determined.

    This is used by the [axicamera](axicamera.v) demonstrator.

11. [hdmi2vga](hdmi2vga.v) converts an incoming 3x10 bit signal, containing
    blue, green, and red channels, into a pixel channel and sync
    signals--stripping out the HDMI signaling along the way.  This turns it into
    what the rest of the repo calls a VGA signal, so that it can now be used
    by the VGA generators or processors.

12. [imgfifo](imgfifo.v) is the actual bus controller.  This module reads
    values from the bus, only to forward them to the video controller one at
    a time.

    This component is in the process of being deprecated for the simple reason
    that the protocol coming out of it is hard to handle.  It will be replaced
    by a more generic Wishbone framebuffer to AXI video stream component.

11. [llvga](llvga.v), a low level VGA controller.  This controller primarily
    just generates the various video control signals--horizontal and vertical
    syncs, end of line flags, end of frame flags, *and* the valid data pixel
    flag used to move the video processing frame forward.

    This component has been deprecated in favor of the [axisvga](axisvga.v)
    component in this same directory. 

12. [pix2stream](pix2stream.v) converts a AXI stream of pixel data into
    packed data such as might be used in a memory bus.  This conversion
    includes options for gray scale, and reduced color options.

13. [sfifo](sfifo.v) is a basic, clock synchronous FIFO implementation.

14. [skidbuffer](skidbuffer.v) is a basic [skidbuffer](https://zipcpu.com/blog/2019/05/22/skidbuffer.html) implementation.

15. [sync2stream](sync2stream.v) converts an incoming (digitized) VGA video
    signal, containing horizontal and vertical synchronization signals together
    with their associated pixel values, into an AXI stream video signal.
    TLAST and TUSER are generated.  In the process, most of the components of
    the mode line are discovered.

16. [tfrvalue](tfrvalue.v) safely moves a value from one clock domain to another
    while also guaranteeing that the bits of the value will all move from one
    clock domain to the other together.  This is used for moving values, such as
    framing information (pixels per line, etc.) from the memory clock domain to
    the pixel clock domain or back again.

17. [transferstb](transferstb.v) safely moves a strobe value from one clock
    domain to another.  For the purposes of this core, a strobe is a single
    (rare) pulse.  Since there is no backpressure, there strobe generator is
    responsible for making sure that no more strobes are generated than can
    safely cross clock domains, lest one be lost in the process.
 
18. [vgatestsrc](vgatestsrc.v), is just a simple test source.  It generates a
    series of color bars.  As a fascinating aside, there's also a divide
    function within this module.  This divide is used to make certain the
    color bars are in the right place.

19. [vidstream2pix](vidstream2pix.v) converts an AXI stream generated from
    memory, such as from the [axivdisplay](axivdisplay.v) controller, to an
    AXI pixel stream.  This includes potentially unpacking several pixels from
    each memory word if necessary.

20. [wbvgaframe](wbvgaframe.v) is the top level module pulling all of these
    components together.  This file is a component of the
    [bench test demo](../bench/rtl/demo.v),
    and would be the file you would include in your design should you wish
    to try it out.  (You'll also need the others, in order to have it work.)

Other AXI video stream only components can also be found in the [gfx](gfx/)
subdirectory.
