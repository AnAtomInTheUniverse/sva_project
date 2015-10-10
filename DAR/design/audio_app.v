/*--------------------------------------------------------------------------------*/
/* Homework assignment for "Introduction to HW Functional Verification with VERA" */
/*                   Copyright 2002 : A. Fasan, N. Arreguy                        */
/*--------------------------------------------------------------------------------*/
/* Module name: audio_app                                                         */
/* File   name: audio_app.v                                                       */
/* Notes: Although this design represents a dedicated DSP block for an audio      */
/* application (digital mixer, digital riverberation, etc.) it has been built for */
/* educational purposes.                                                          */
/* Description: there are 4 inputs and 4 outputs: these are compatible with 16    */
/* bits PCM format.                                                               */
/* Every input can be processed by its own dedicated delay line: every delay line */
/* is programmable.                                                               */
/* The delay lines are programmable via a serial interface: one of the internal   */
/* blocks ("delay_prgrm") contains the logic needed to access and program the     */
/* length of each delay line.                                                     */
/* Version 0.0: original version after specs                                      */
/* Version 0.1: bug fixes                                                         */
/* Version 0.2: added clk_a for audio and clk_s for serial port                   */
/* Version 2.0: removed  clk_a for audio and clk_s for serial port                */
/* Version 2.0: added single clock input, and single reset                        */
/*--------------------------------------------------------------------------------*/

`include "defines.vh"

module audio_app (
            clk, rst_ 
           ,di_0, di_1, di_2, di_3
           ,do_0, do_1, do_2, do_3
           ,prgrm_in, prgrm_go_, err_);
input  clk;
input  rst_;
input  prgrm_in;
input  prgrm_go_;
input  [`PCM - 1 : 0] di_0, di_1, di_2, di_3;
output [`PCM - 1 : 0] do_0, do_1, do_2, do_3;
output                err_ ;

wire [3:0] prog_ctl; // each bit activates the corresponding programable delay line
wire [`D_DEPTH - 1 : 0] prog_delay;

delay_prgrm host   (clk, rst_, prgrm_in   ,prgrm_go_   , prog_ctl, prog_delay, err_);
delay_line  dline0 (clk, rst_, prog_ctl[0], prog_delay, di_0   , do_0);
delay_line  dline1 (clk, rst_, prog_ctl[1], prog_delay, di_1   , do_1);
delay_line  dline2 (clk, rst_, prog_ctl[2], prog_delay, di_2   , do_2);
delay_line  dline3 (clk, rst_, prog_ctl[3], prog_delay, di_3   , do_3);

endmodule
