## Controller

This repository contains a [Video Controller](rtl/wbvgaframe.v).  This
controller includes not only the [low-level framer](rtl/llvga.v), but also
a [bus controller](rtl/imgfifo.v) to read values from memory to then be
displayed on the screen.  This is the basis of a frame buffer approach to
video.

This capability is fully demonstrated via the [Verilator based](http://zipcpu.com/blog/2017/06/21/looking-at-verilator.html) simulator.

## Simulation

This repository also contains a basic [video simulator](bench/cpp/vgasim.cpp).
It takes video inputs from a Verilated [design module](bench/rtl/demo.v),
and draws them to the screen.  All [video modes](bench/cpp/videomode.h)
are supported by simply creating the [simulator object](bench/cpp/vgasim.cpp)
with the appropriate mode lines, although the [memory initialization
file](bench/cpp/slide.hex) is specifically formatted for a 1280x1024 screen.
The [simulator](bench/cpp/vgasim.cpp) will then create a window of that size
on any GTK enabled screen (i.e. Linux), displaying whatever image [your
design](rtl/wbvgaframe.v) is producing.

The repository also contains a [test pattern generator](rtl/vgatest.v) modeled
roughly after a standard VGA pattern, although not quite the same.  As mentioned
above, there's also a frame buffered approach to drawing on the window
centered around a [wishbone enabled memory driver](rtl/imgfifo.v).  This
second capability will draw a more arbitrary image on the display.

References to VGA within this module could just as easily refer to any display.
Be careful that you match the proper polarity of the synch pulses.

## Building

There is a [master Makefile](Makefile) in this directory.  Hence, to build
this project you should be able to just clone it,
`git clone https://github.com/ZipCPU/vgasim`, run `make` in the main
directory, and then run `main_tb` from within the
`bench/cpp` directory.

The project does depend upon having both Verilator and gtkmm-3.0 installed.

## License

All of the source code in this repository is released under the
[GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html).  If these conditions
are not sufficient for your needs, other licenses terms may be purchased.

