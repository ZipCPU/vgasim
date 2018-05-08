This directory contains an example design containing the extra logic
necessary for running the video driver from memory.  [demo.v](demo.v) is the
main/master file.  It contains references to both the (simulated) block RAM
memory device [memdev](memdev.v), as well as the Wishbone VGA controller
[wbvgaframe](../../rtl/wbvgaframe.v).
