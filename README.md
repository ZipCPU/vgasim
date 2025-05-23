## Controller

This repository contains a couple of [Video Controller](rtl/wbvgaframe.v)s.

The original [Video Controller](rtl/wbvgaframe.v)
includes not only the [low-level framer](rtl/llvga.v), but also
a [bus controller](rtl/imgfifo.v) to read values from memory to then be
displayed on the screen.  This is the basis of a frame buffer approach to
video.  This capability is fully demonstrated via the [Verilator
based](http://zipcpu.com/blog/2017/06/21/looking-at-verilator.html) simulator.

There are now also two AXI-based cores.  The first is an [AXI-based Video
Controller](rtl/axivideo.v) that can produce either VGA or HDMI signals.  This
controller is demonstrated via a [slightly different
simulator](bench/cpp/axi_tb.cpp), including simulations for both
[VGA](bench/cpp/vgasim.cpp) and [HDMI](bench/cpp/hdmisim.cpp).
The [second AXI-based video controller will record incoming video signals to
memory](rtl/axicamera.v).  The incoming capability is [demonstrated via
a simulation](bench/rtl/axirepeater.v) to capture a piece of your screen via
an [HDMI source simulator](bench/cpp/hdmisource.cpp), [write it to an AXI-based
block RAM frame buffer memory](rtl/axivcamera.v), and then to [read it back out
again](rtl/axivdisplay.v) to feed a GTK++ window.

## Simulation

This repository also contains two basic [video simulator](bench/cpp/vgasim.cpp)
components.  The first, either [VGASIM](bench/cpp/vgasim.cpp)
or [HDMISIM](bench/cpp/hdmisim.cpp) takes video outputs from a
Verilated [design module](bench/rtl/demo.v) and displays them on your screen
as though it were the monitor the design was displaying to, and the
[second](bench/cpp/vgasource.cpp) takes a piece of your screen and creates
either [a VGA source signal](bench/cpp/vgasource.cpp) or [an HDMI source
signal](bench/cpp/hdmisource.cpp) with it.

All [video modes](bench/cpp/videomode.h)
are supported by simply creating the [simulator object](bench/cpp/vgasim.cpp)
with the appropriate mode lines, although the [memory initialization
file](bench/cpp/slide.hex) for the [outgoing demo](bench/rtl/demo.v) is
specifically formatted for a 1280x1024 screen.
The [simulator](bench/cpp/vgasim.cpp) will then create a window of that size
on any GTK enabled screen (i.e. Linux), displaying whatever image [your
design](rtl/wbvgaframe.v) is producing.

The repository also contains a [test pattern generator](rtl/vgatestsrc.v)
modeled roughly after a standard VGA pattern, although not quite the same.  As
mentioned above, there's also a frame buffered approach to drawing on the window
centered around a [wishbone enabled memory driver](rtl/imgfifo.v).  This
second capability will draw a more arbitrary image on the display.

References to VGA within this module could just as easily refer to any display.
Be careful that you match the proper polarity of the sync pulses.

## Building

There is a [master Makefile](Makefile) in this directory.  Hence, to build
this project you should be able to just clone it,
`git clone https://github.com/ZipCPU/vgasim`, run `make` in the main
directory, and then run one of the test programs, such as `main_tb`, from
within the `bench/cpp` directory.  For those that display images from the
frame buffer, such as `main_tb` or `axi_tb`, be sure to wait long enough
to see the outgoing image from the frame buffer--it takes a few seconds.

The project depends upon having both Verilator and gtkmm-3.0 installed.

## License

All of the source code in this repository is released under the
[GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html).  If these conditions
are not sufficient for your needs, other licenses terms may be purchased.
