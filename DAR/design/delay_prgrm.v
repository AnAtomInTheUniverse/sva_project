/*--------------------------------------------------------------------------------*/
/* Homework assignment for "Introduction to HW Functional Verification with VERA" */
/*                   Copyright 2002 : A. Fasan, N. Arreguy                        */
/*--------------------------------------------------------------------------------*/
/* Module name: delay_prgrm                                                       */
/* File   name: delay_prgrm.v                                                     */
/* Notes: This module is accessed serially: only write mode (for now: it is not   */
/* possible to read the registers back)                                           */
/* This is the module that will program the delay lines via prog_delay            */
/* Description:                                                                   */
/*

   prgrm_go_ -----+__________________________+---------------

   prgrm_in ------< valid    serial   data  >------
                  < 1 bit >                          Low == Write
                           < 2 bits >                Select one of 4 delay lines
                                     <3 bits>        Select 1-8 cycle delays for line
  
This Host Control Serial Interface module will control from one to four serial delay
lines for a digital Reverberation Module.

Each delay line's delay can be programmed for from 1 to 8 cycle delays

Serial bits go LSB in first into the prgrm_in

prgrm_go_ must be asserted while valid serial data is applied. If prgrm_go_ is
de-asserted, then the serial data must be reapplied from the start. 

If prgrm_go_ is deasserted during a program cycle, err_ will be asserted low for
one cycle.

Additional Notes: 
  0.0   original version
  0.1   02/01/04 general clean up, prog_delay & prog_ctl zero when !go_ 
  1.0   02/06/23 modifications to state machine.
  2.0   02/07/06 major mods to state machines including ERROR state
                 prgram_go_ is made active low
*/
/*--------------------------------------------------------------------------------*/

`include "defines.vh"
`define DEPTH  [`D_DEPTH - 1 : 0]

module delay_prgrm (clk, rst_, prgrm_in, prgrm_go_, prog_ctl, prog_delay, err_);
    input  clk, rst_ ;
    input  prgrm_in ;
    input  prgrm_go_ ;
    output err_ ;
    output  [3:0] prog_ctl;
    output `DEPTH prog_delay;
    reg    `DEPTH delay     , nxt_delay     ; // programmed delay value
    reg     [1:0] ctrl      , nxt_ctrl      ; // contrls sel'n of 1-4 delay lines to program
    reg     [1:0] counter   , nxt_counter   ; // internal counter
    reg     [2:0] state     , nxt_state     ;
    reg     [2:0] last_state, last_nxt_state;
    reg           go_       , nxt_go_       ; // enables control, delay values onto signals
    reg           err_      , nxt_err_      ; // enables control, delay values onto signals

    //------------------------------------
    // Registers
    //------------------------------------
    always @(posedge clk) state   <= (rst_ == 1'b0)?  `IDLE    : nxt_state ;
    always @(posedge clk) counter <= (!rst_)?         2'b00    : nxt_counter ;
    always @(posedge clk) ctrl    <= (!rst_)?         2'b11    : nxt_ctrl ;
    always @(posedge clk) delay   <= (!rst_)?         4'b0000  : nxt_delay ;
    always @(posedge clk) go_     <= (!rst_)?         1'b1     : nxt_go_ ;
    always @(posedge clk) err_    <= (!rst_)?         1'b1     : err_   ;

    //----------------------------------------------------
    // output to delay lines
    // if !go_, state machine recognized valid serial input
    //----------------------------------------------------
    assign prog_delay = !go_? delay         : 3'b000  ;
    assign prog_ctl   = !go_? decode(ctrl)  : 4'b1111 ;

    //------------------------------------
    // State machine for serial input
    //------------------------------------
  always @(state or prgrm_go_ or prgrm_in or counter )
  begin
	nxt_state   = state   ;
	nxt_ctrl    = ctrl    ;
	nxt_go_     = go_     ;
	nxt_delay   = delay   ;
        nxt_err_    = err_    ;
	nxt_counter = counter ;

	case(state)
	  `IDLE: begin
		nxt_ctrl    = 2'b11 ;
		nxt_go_     = 1'b1 ;
		nxt_delay   = 3'b000 ;
		nxt_err_    = 1'b1 ;
		nxt_counter = 2'b00 ;

                case (prgrm_go_)
		  1'b0 :                                     // prgrm_go_ valid
                    begin
                      case (prgrm_in)                        // prgrm_in  write
                        1'b0 : begin
                             nxt_state   = `WRITE_SELECT ;
                             nxt_counter =  2'b00 ;
                        end // 1'b0
                        1'b1 : begin
                             nxt_state = `READ;              // prgrm_in  read
                        end 
                      endcase // prgrm_in
                    end // 1'b0 
                  1'b1 :
                    begin
                      nxt_state = `IDLE ;
                    end
                endcase // (prgrm_go_)                       // end prgrm_go_ valid
	    end  // end IDLE

	   `WRITE_SELECT: begin
                case (prgrm_go_)                             // prgrm_go_ valid
                  1'b0 :
                    begin
		      nxt_ctrl[counter] = prgrm_in;
                      case (counter)
                        2'b00 : begin                        // 
			     nxt_counter = counter ;
			     nxt_counter = nxt_counter + 1 ;
			     nxt_state   = `WRITE_SELECT ;
                        end
                        2'b01 : begin                        // 
			     nxt_counter = 2'b00;            // decrement counter 
			     nxt_state = `WRITE_DELAY;
			end
			default : begin                     // counter is in error
		             nxt_state = `ERROR ;
			   end
		      endcase // counter
                    end  // 1'b0
                  1'b1 : begin                              // prgrm_go_ !valid
		        nxt_state = `ERROR;
                    end  // 1'b1
	        endcase  // prgrm_go_
	    end  // WRITE_SELECT

	    `WRITE_DELAY: begin
                case (prgrm_go_)                             // prgrm_go_ valid
                  1'b0 :
                    begin
		      nxt_delay[counter] =  prgrm_in ;
                      case (counter)
			2'b00 :                              // continue reading delay 
			   begin
			    nxt_counter =  counter ;
			    nxt_counter =  nxt_counter + 2'b01;
                            nxt_state   = `WRITE_DELAY ;
			   end
			2'b01 :                              // continue reading delay
			   begin
			    nxt_counter =  counter ;
			    nxt_counter =  nxt_counter + 2'b01;
                            nxt_state   = `WRITE_DELAY ;
			   end
			2'b10 :                             // delay valid, assert go_
			   begin
			    nxt_counter =  2'b00;
                            nxt_state   = `IDLE ;
			    nxt_go_     = 1'b0;
			   end
			2'b11 :                             // delay !valid
			   begin
			    nxt_go_   = 1'b1;
                            nxt_state = `ERROR ;
			   end
                      endcase // (counter)
		    end  // prgrm_go_ = 1'b0
                  1'b1 : begin                              // prgrm_go_ !valid
			   begin
			    nxt_go_   = 1'b1;
		            nxt_state = `ERROR;
			   end
                    end  // 1'b1
	        endcase  // prgrm_go_
              end

	    `READ: begin
		nxt_state = `ERROR;
		nxt_go_   = 1'b1;
	      end
	    `ERROR: begin
		nxt_state = `IDLE;
                nxt_err_  = 0'b0 ;
		nxt_go_   = 1'b1;
	       end
	    default: begin
		nxt_state = `ERROR;
		nxt_go_   = 1'b1;
	       end
		endcase 
	end

    //-------------------------------------------------
    //decoder function to select the correct delay line
    //-------------------------------------------------
     function [3:0] decode;
      input   [1:0] ctrl;
      reg     [3:0] decode_ctrl;
      begin
    	    case(ctrl)
	    2'b00 : decode_ctrl = 4'b1110 ;
	    2'b01 : decode_ctrl = 4'b1101 ;
	    2'b10 : decode_ctrl = 4'b1011 ;
	    2'b11 : decode_ctrl = 4'b0111 ;
	endcase
       decode = decode_ctrl;
      end
     endfunction


`ifdef DEBUG
  //------------------------------------
  // ADDED FOR DEBUGGING
  //------------------------------------
  // to turn off debug statements do either of the following :
  // Comment $display statements
  // Do not use the +define+DEBUG compile time option when compiling this module

  always @(negedge go_)
    $display("vlog: ### go_ asserted prog_delay=%b prog_ctl=%b time=%d"
                  , prog_delay, prog_ctl, $time) ;

  always @(posedge clk) $display("^^^^^^ Posedge Clock: state  =%b :t=%d",state, $time) ;
  always @(posedge clk) $display("^^^^^^ Posedge Clock: counter=%b",counter) ;
  always @(posedge clk) $display("^^^^^^ Posedge Clock: ctrl   =%b",ctrl) ;
  always @(posedge clk) $display("^^^^^^ Posedge Clock: delay  =%b",delay) ;

  always @(state or prgrm_go_ or prgrm_in or counter )
  begin
    $display("vlog: ############################ STATE ############################") ;
    $display("vlog: prgrm_go_=%b prgrm_in=%b counter=%b ctrl=%b go_=%b rst_=%b"
                   ,prgrm_go_   ,prgrm_in   ,counter   ,ctrl   ,go_   ,rst_) ;
    // if (state != last_state)
     begin
       case(state)
        `IDLE         : $display("vlog: STATE = IDLE") ;
        `WRITE_SELECT : $display("vlog: STATE = WRITE_SELECT") ;
        `WRITE_DELAY  : $display("vlog: STATE = WRITE_DELAY") ;
        `READ         : $display("vlog: STATE = READ") ;
        `ERROR        : $display("vlog: STATE = ERROR") ;
         default      : $display("vlog: STATE = default") ;
       endcase
       // last_state = state ;
    end // if
  end // state

  always @(nxt_state or prgrm_go_ or prgrm_in or nxt_counter )
  begin
    $display("vlog: ######################## nxt_STATE ############################") ;
    // if (nxt_state != last_nxt_state)
     begin
       case(nxt_state)
        `IDLE         : $display("vlog: nxt_STATE = IDLE") ;
        `WRITE_SELECT : $display("vlog: nxt_STATE = WRITE_SELECT") ;
        `WRITE_DELAY  : $display("vlog: nxt_STATE = WRITE_DELAY") ;
        `READ         : $display("vlog: nxt_STATE = READ") ;
        `ERROR        : $display("vlog: nxt_STATE = ERROR") ;
         default      : $display("vlog: nxt_STATE = default") ;
       endcase
       last_nxt_state = nxt_state ;
     end // if
  end // nxt_state

`endif
endmodule
