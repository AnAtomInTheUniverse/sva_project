/*--------------------------------------------------------------------------------*/
/* Homework assignment for "Introduction to HW Functional Verification with VERA" */
/*                   Copyright 2002 : A. Fasan, N. Arreguy                        */
/*--------------------------------------------------------------------------------*/
/* Module name: delay_line                                                        */
/* File   name: delay_line.v                                                      */
/* Version    : 0.2                                                               */
/* Date       : 4/5/2001                                                          */
/* Notes: This is the delay line, it is programmed via prog_ctl_ and prog_delay    */
/*
// 
// prog_ctl_ and prog_delay 
//            P----+ // the programmed value decides where to tap the delay line
//                 v
// idata  -> D - D - D - D - D - D - D - D ->
//                 |
//                 +----------------> odata
// 
//   Additional Notes:
//   0.0        original version
//   0.1        parametrized version
//   0.2        prog_ctl_ and prog_delay are now signals that belong
//              to different clock domains
*/
/*--------------------------------------------------------------------------------*/
/* 020623 removed synchronizers */

`include "defines.vh"

module  delay_line (clk, rst_, prog_ctl_, prog_delay, idata, odata);
    input                     clk, rst_ ;
    input                     prog_ctl_;
    input  [`PCM     - 1 : 0] idata ;
    input  [`D_DEPTH - 1 : 0] prog_delay;
    output [`PCM     - 1 : 0] odata ;
   
    reg    [`D_DEPTH - 1 : 0] delay_value;
    reg    [`PCM     - 1 : 0] delay [7:0];


    always @(posedge clk) delay_value   <=  (!rst_)?       3'b000     : 
                                           ((!prog_ctl_)?  prog_delay : delay_value) ;
`ifdef DEBUG
    always @(delay_value)
	  $display(" ##### delay_line  :  programed with program delay = %0d\n", delay_value) ;
`endif

    assign odata   =  delay[delay_value] ;

    always @(posedge clk) delay[0] <= (!rst_)? 16'h00_00 : idata ;
    always @(posedge clk) delay[1] <= (!rst_)? 16'h00_00 : delay[0] ;
    always @(posedge clk) delay[2] <= (!rst_)? 16'h00_00 : delay[1] ;
    always @(posedge clk) delay[3] <= (!rst_)? 16'h00_00 : delay[2] ;
    always @(posedge clk) delay[4] <= (!rst_)? 16'h00_00 : delay[3] ;
    always @(posedge clk) delay[5] <= (!rst_)? 16'h00_00 : delay[4] ;
    always @(posedge clk) delay[6] <= (!rst_)? 16'h00_00 : delay[5] ;
    always @(posedge clk) delay[7] <= (!rst_)? 16'h00_00 : delay[6] ;

endmodule
