This repository contains a simple [video simulator](bench/cpp/vgasim.cpp).  It
takes video inputs from a Verilated [design module](rtl/llvga.v), and draws
them to the screen.  All [video modes](bench/cpp/videomode.h) are supported by
simply creating the [simulator object](bench/cpp/vgasim.cpp) with the
appropriate mode lines.  The [simulator](bench/cpp/vgasim.cpp) will then
create a window on the screen, displaying whatever image
[your design](rtl/wbvgaframe.v) is producing.

The repository also contains a [test pattern generator](rtl/vgatest.v) modeled
roughly after a standard VGA pattern, although not quite the same.

References to VGA within this module could just as easily refer to any display.
Be careful that you match the proper polarity of the synch pulses.

## Building

I haven't yet built a master makefile.  Until I do, just run make in the
[rtl](rtl/) directory followed by make in the [bench/cpp](bench/cpp/)
directory.  The demo code will then be found in [bench/cpp/main_tb](bench/cpp/main_tb).

The project does depend upon having both Verilator and gtkmm-3.0 installed.

## License

All of the source code in this repository is released under the
[GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html).  If these conditions
are not sufficient for your needs, other licenses terms may be purchased.

