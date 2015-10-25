`timescale 1ns/1ns
module audio_app_test_top;
  parameter simulation_cycle = 100 ;
  
  logic  SystemClock ;
  logic  SystemReset_ ;
  logic  clk ;
  logic  rst_ ;
  logic  [15:0]  di_0 ;
  logic  [15:0]  di_1 ;
  logic  [15:0]  di_2 ;
  logic  [15:0]  di_3 ;
  logic  [15:0]  do_0 ;
  logic  [15:0]  do_1 ;
  logic  [15:0]  do_2 ;
  logic  [15:0]  do_3 ;
  logic  prgrm_in ;
  logic  prgrm_go_ ;
  logic  err_ ;
  assign  clk = SystemClock ;
  assign  rst_ = SystemReset_ ;

  //--------------------
  // Testbench temp vars
  //--------------------
  logic [2:0]   tap_val [4];
  logic [1:0]	dl;
  logic [2:0]	delay_val;

  audio_app dut(
    .clk  ( clk ),
    .rst_ ( rst_ ),
    .di_0 ( di_0 ),
    .di_1 ( di_1 ),
    .di_2 ( di_2 ),
    .di_3 ( di_3 ),
    .do_0 ( do_0 ),
    .do_1 ( do_1 ),
    .do_2 ( do_2 ),
    .do_3 ( do_3 ),
    .prgrm_in ( prgrm_in ),
    .prgrm_go_ ( prgrm_go_ ),
    .err_ ( err_ )
  );

  task move_tap;
	input op;
	input [2:0] delay_amt;
	input [1:0] delay_line;
    @(negedge SystemClock);
    prgrm_go_	=	1'b0;
    prgrm_in	=	op;
    @(negedge SystemClock);
    prgrm_in	=	delay_line[0];
    @(negedge SystemClock);
    prgrm_in	=	delay_line[1];
    @(negedge SystemClock);
    prgrm_in	=	delay_amt[0];
    @(negedge SystemClock);
    prgrm_in	=	delay_amt[1];
    @(negedge SystemClock);
    prgrm_in	=	delay_amt[2];
    @(negedge SystemClock);
    prgrm_go_	=	1'b1;
	prgrm_in	=	1'b0;
	tap_val[delay_line]	=	delay_amt;
  endtask
  
  initial begin
    SystemClock = 0 ;
    forever begin
      #(simulation_cycle/2) 
        SystemClock = ~SystemClock ;
    end
  end


  initial begin
    SystemReset_ 	= 1'b0;
    prgrm_in 		= 1'b0;
	prgrm_go_		= 1'b1;

	repeat(10) @(posedge SystemClock);
    SystemReset_ = 1'b1;
	

	// --------------------
	// Reset Signal Testing
	// --------------------
	// Feed in non-zero values to each delay line
	// Set delay to 7 and then assert reset - Make
	// sure that all of the outputs are 0 after 
	// after reset asserts for at least 2 cycles
	@(negedge SystemClock);
	di_0	=	16'h00_11;
	di_1	=	16'h00_22;
	di_2	=	16'h00_44;
	di_3	=	16'h00_88;
	move_tap(1'b0, 3'b111, 2'b00);
	move_tap(1'b0, 3'b111, 2'b01);
	move_tap(1'b0, 3'b111, 2'b10);
	move_tap(1'b0, 3'b111, 2'b11);

	repeat(6) @(posedge SystemClock);

	@(negedge SystemClock);
	SystemReset_	=	1'b0;
	
	repeat(2) @(posedge SystemClock);
	@(negedge SystemClock);
	SystemReset_	=	1'b1;
	@(posedge SystemClock);
	move_tap(1'b0, 3'b111, 2'b00);
	move_tap(1'b0, 3'b111, 2'b01);
	move_tap(1'b0, 3'b111, 2'b10);
	move_tap(1'b0, 3'b111, 2'b11);
	
	// -----------------
	// Delay Tap Testing 
	// -----------------
	@(negedge SystemClock);
	SystemReset_	=	1'b0;
	
	repeat(2) @(posedge SystemClock);

	@(negedge SystemClock)
	SystemReset_	=	1'b1;
	move_tap(1'b0, 3'b111, 2'b00);

	@(negedge SystemClock);
	di_0	=	16'hAA_AA;
	for(int i = 0; i < 8; i++) begin
		assert(do_0 == 16'h00_11) else $error("Delay tap gets value too early!");
		@(negedge SystemClock);
	end

	// Send in sequentially increasing input data on
	// delay line 0, set delay tap to 7 and then 
	// check that the output appears exactly 8 cycles
	// later. 
	@(negedge SystemClock);
	SystemReset_	=	1'b0;

	repeat(2) @(posedge SystemClock);

	@(negedge SystemClock);
	SystemReset_	=	1'b1;
	di_0 			=	16'h00_00;
	move_tap(1'b0, 3'b111, 2'b00);
	for(int i = 0; i < 16; i++) begin
			@(negedge SystemClock);
			di_0	+= 16'h00_01;
	end
	
	// Set different delay taps for each delay line
	// apply same input value to each line and then
	// check if the output appears with correct 
	// programmed delay for each line AND also make
	// sure that there is no interference between 
	// delay lines - setting the tap to a certain value
	// for a line should NOT affect the delay of another
	// line. 
	@(negedge SystemClock);
	SystemReset_	=	1'b0;

	repeat(2) @(posedge SystemClock);

	@(negedge SystemClock);
	SystemReset_	=	1'b1;
	di_0			=	16'h00_00;
	di_1			=	16'h00_00;
	di_2			=	16'h00_00;
	di_3			=	16'h00_00;
	move_tap(1'b0, 3'b010, 2'b00);
	move_tap(1'b0, 3'b011, 2'b01);
	move_tap(1'b0, 3'b100, 2'b10);
	move_tap(1'b0, 3'b101, 2'b11);
	
	@(negedge SystemClock);
	di_0			=	16'hFF_FF;
	di_1			=	16'hFF_FF;
	di_2			=	16'hFF_FF;
	di_3			=	16'hFF_FF;
	@(negedge SystemClock);
	di_0			=	16'h00_00;
	di_1			=	16'h00_00;
	di_2			=	16'h00_00;
	di_3			=	16'h00_00;

	repeat(3) @(posedge SystemClock);
	dl_0: assert((do_0 == 16'hFF_FF) && (do_1 == 16'h00_00) && (do_2 == 16'h00_00) && (do_3 == 16'h00_00)) else $display("Incorrect delay on line 0!");
	@(posedge SystemClock);
	dl_1: assert((do_1 == 16'hFF_FF) && (do_2 == 16'h00_00) && (do_3 == 16'h00_00)) else $display("Incorrect delay on line 1!");
	@(posedge SystemClock);
	dl_2: assert((do_2 == 16'hFF_FF) && (do_3 == 16'h00_00)) else $display("Incorrect delay on line 2!");
	@(posedge SystemClock);
	dl_3: assert(do_3 == 16'hFF_FF) else $display("Incorrect delay on line 3!");

	
	// Cycle through all delay tap values (0 -> 7)
	// for each delay line and check whether the output
	// delay matches the programmed delay
	@(negedge SystemClock);
	SystemReset_	=	1'b0;

	repeat(2) @(posedge SystemClock);

	@(negedge SystemClock);
	SystemReset_	=	1'b1;
	for(int i = 0; i < 4 ; i++)	begin
		dl	=	(i == 0) ? 2'b00 : (i == 1) ? 2'b01 : (i == 2) ? 2'b10 : 2'b11;
		for(int j = 0; j < 50; j++) begin
			delay_val		=	$random %8;
			move_tap(1'b0, delay_val, dl);

			if(i == 0) begin
				@(negedge SystemClock);
				di_0			=	$random;
			end
			else if (i == 1) begin
				@(negedge SystemClock);
				di_1			=	$random;
			end
			else if	(i == 2) begin
				@(negedge SystemClock);
				di_2			=	$random;
			end
			else begin
				@(negedge SystemClock);
				di_3			=	$random;
			end

			repeat(delay_val+2) @(posedge SystemClock);
			if(i == 0)
				rand_dl_0:assert(do_0	==	di_0) else $display("Delay line 0 failed random delay test");
			else if(i == 1)
				rand_dl_1:assert(do_1	==	di_1) else $display("Delay line 0 failed random delay test");
			else if(i == 2)
				rand_dl_2:assert(do_2	==	di_2) else $display("Delay line 0 failed random delay test");
			else if(i == 3)
				rand_dl_3:assert(do_3	==	di_3) else $display("Delay line 0 failed random delay test");
		end
	end

//	delay_check: assert property (@(posedge SystemClock) (do_0 == $past(di_0, dl_0_tap))) else $display("FAIL!");
	



	//-------------------------
	// Testing READ Mode Error
	//-------------------------
	// Try programming in read mode and 
	// check to see if err_ signal is asserted
	@(negedge SystemClock);
	SystemReset_	=	1'b0;

	repeat(2) @(posedge SystemClock);
	
	@(negedge SystemClock);
	SystemReset_	=	1'b1;
	move_tap(1'b1, 3'b010, 2'b00);

    // terminate simulation
    // FIXME: change simulation time if necessary
    #40000 $finish;
  end
  
  //initial begin
  //  $dumpfile("./obj/verilog.dump");
  //  $dumpvars(0,audio_app_test_top);
  //end

  //
  // CREATE YOUR TESTBENCH BELOW
  //

  //----------------------------
  //		 ASSERTIONS
  //----------------------------
  
  //----------------
  //Reset Assertions
  //----------------
  // All outputs should be zero immediately after rst_ is asserted
   prop_assert_rst_: assert property (@(posedge SystemClock) disable iff((di_0 === 'x ) && (di_1 === 'x) && (di_2 === 'x) && (di_3 === 'x))
   										(!SystemReset_) |=> (do_0 == 16'h0000) && (do_1 == 16'h0000) && (do_2 == 16'h0000) && (do_3 == 16'h0000));

  //---------------------
  //Err Signal Assertions
  //---------------------
  // prgrm_go cannot be deasserted (1'b1) during the 6 cycles of delay programming
  prop_prgrm_go_deasserted: assert property (@(posedge SystemClock) 
  												disable iff (!SystemReset_) ((prgrm_go_ ##1 !prgrm_go_) ##[1:5] prgrm_go_ )|=> !err_);
  // err_ should assert (1'b0) if bit0 of prgrm_in is 1 during programming 
  // since Read mode is not supported by design
  prop_prgrm_rd_err: assert property (@(posedge SystemClock) 
  										disable iff (!SystemReset_) (err_ && prgrm_go_) ##1 (!prgrm_go_ && prgrm_in) |=> !err_);

  // err_ should only be asserted (1'b0) for 1 cycle
  prop_err_one_cycle: assert property (@(posedge SystemClock) 
  										disable iff (!SystemReset_) (!err_ |=> err_));
  //------------------------
  //Program Delay Assertions
  //------------------------
  




endmodule
