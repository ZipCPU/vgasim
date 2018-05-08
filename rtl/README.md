This directory contains a couple of valuable video components within it.

1. [atxfifo](atxfifo.v) is an asynchronous FIFO, modified to also produce an
   (estimate) of the fill within the FIFO so as to know when to start refilling
   it.

2. [imgfifo](imgfifo.v) is the actual bus controller.  This module reads values
   from the bus, only to forward them to the video controller one at a time.

3. [llvga](llvga.v), a low level VGA controller.  This controller primarily
   just generates the various video control signals--horizontal and vertical
   syncs, end of line flags, end of frame flags, *and* the valid data pixel
   flag used to move the video processing frame forward.

4. [vgatestsrc](vgatestsrc.v), is just a simple test source.  It generates a
   series of color bars.  As a fascinating aside, there's also a divide
   function within this module.  This divide is used to make certain the
   color bars are in the right place.

5. [wbvgaframe](wbvgaframe.v) is the top level module pulling all of these
   components together.  This file is a component of the
   [bench test demo](../bench/rtl/demo.v),
   and would be the file you would include in your design should you wish
   to try it out.  (You'll also need the others, in order to have it work.)
