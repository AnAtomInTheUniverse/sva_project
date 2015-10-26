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
  logic [2:0]   tap_val_rpt [4];
  logic [2:0]   tap_val_drop [4];
  logic [1:0]	dl;
  logic [2:0]	delay_val;
  logic			forked_0 = 1'b0;;
  logic			forked_1 = 1'b0;;
  logic			forked_2 = 1'b0;;
  logic			forked_3 = 1'b0;;

  logic			forked_0_drop = 1'b0;;
  logic			forked_1_drop = 1'b0;;
  logic			forked_2_drop = 1'b0;;
  logic			forked_3_drop = 1'b0;;

  logic			forked_0_tap_4 = 1'b0;;
  logic			forked_1_tap_4 = 1'b0;;
  logic			forked_2_tap_4 = 1'b0;;
  logic			forked_3_tap_4 = 1'b0;;

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
  endtask
  
  task reset_all;
	@(negedge SystemClock);
	SystemReset_	=	1'b0;
	repeat(2) @(posedge SystemClock);
	@(negedge SystemClock);
	SystemReset_	=	1'b1;
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

	reset_all();
	@(posedge SystemClock);
	move_tap(1'b0, 3'b111, 2'b00);
	move_tap(1'b0, 3'b111, 2'b01);
	move_tap(1'b0, 3'b111, 2'b10);
	move_tap(1'b0, 3'b111, 2'b11);
	
	// -----------------
	// Delay Tap Testing 
	// -----------------
	reset_all();
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
	reset_all();
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
	reset_all();
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

	
	// Cycle through random delay tap values for
	// each delay line and check whether the output
	// delay matches the programmed delay by comparing
	// the 16 bit random output value exactly delay+1
	// cycles after it was sent in as input. Note that
	// the checking is done delay+2 cycles later as the 
	// assertion checks the prior value of a reg at the 
	// posedge clock transition point 
	reset_all();
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

			/* We perform two checks at the transition
			* point - the first assertion triggers exactly
			* delay+1 cycles after the input was changed but
			* the value has not transitioned yet - so the 
			* output should be the old value*/
			repeat(delay_val+1) @(posedge SystemClock);
			if(i == 0)
				rand_dl_0_old_val:assert(do_0	!=	di_0) else $display("Delay line 0 failed random delay test");
			else if(i == 1)
				rand_dl_1_old_val:assert(do_1	!=	di_1) else $display("Delay line 0 failed random delay test");
			else if(i == 2)
				rand_dl_2_old_val:assert(do_2	!=	di_2) else $display("Delay line 0 failed random delay test");
			else if(i == 3)
				rand_dl_3_old_val:assert(do_3	!=	di_3) else $display("Delay line 0 failed random delay test");

			/* The output should have transitioned to the
			* new value at the next edge so we assert that
			* the ouput is the new value that was programmed
			* in with delay delay_val*/
			@(posedge SystemClock);
			if(i == 0)
				rand_dl_0_new_val:assert(do_0	==	di_0) else $display("Delay line 0 failed random delay test");
			else if(i == 1)
				rand_dl_1_new_val:assert(do_1	==	di_1) else $display("Delay line 0 failed random delay test");
			else if(i == 2)
				rand_dl_2_new_val:assert(do_2	==	di_2) else $display("Delay line 0 failed random delay test");
			else if(i == 3)
				rand_dl_3_new_val:assert(do_3	==	di_3) else $display("Delay line 0 failed random delay test");
		end
	end

	//--------------------------------------------
	// Testing Data word drop due to Reprogramming
	// -------------------------------------------
	/* In this section we test the correct reprogrammability
	* of the delay tap in each line. Given an input sequence 
	* of known data values, if the tap is reprogrammed during
	* the sequence, the number of data words dropped should
	* be a function of the new and old positions of the delay
	* tap (MAX DROP = 7, MAX REPEAT = 7) 
	
	* Feed in data words starting at random values and incrementing
	* by 1 each cycle. Then, we move the tap by a specific amount
	* and assert that the output after the reprogramming is complete
	* must be the value of the input from 7 cycles prior*/
	reset_all();

	di_0	=	$random;	//16'h00_00;
	di_1	=	$random;	//16'h00_00;
	di_2	=	$random;	//16'h00_00;
	di_3	=	$random;	//16'h00_00;
	fork begin
		for(int i = 0; i < 50; i++) begin
			@(negedge SystemClock);
			di_0	+=	 1;
			di_1	+=	 1;
			di_2	+=	 1;
			di_3	+=	 1;
		end
	end
	begin
		delay_val	=	3'b111;
		move_tap(1'b0, delay_val, 2'b00);
		forked_0 = 1'b1;
		move_tap(1'b0, delay_val, 2'b01);
		forked_1 = 1'b1;
		move_tap(1'b0, delay_val, 2'b10);
		forked_2 = 1'b1;
		move_tap(1'b0, delay_val, 2'b11);
		forked_3 = 1'b1;
	end
	
	join
	forked_0 = 1'b0;
	forked_1 = 1'b0;
	forked_2 = 1'b0;
	forked_3 = 1'b0;

	/* Now we test the opposite case - moving the tap 
	* from 7 to 0. We should see no more than 7 words 
	* of data dropped.*/
	repeat(10) @(posedge SystemClock);
	reset_all();
	// Programming the taps to 7
	move_tap(1'b0, 3'b111, 2'b00);
	move_tap(1'b0, 3'b111, 2'b01);
	move_tap(1'b0, 3'b111, 2'b10);
	move_tap(1'b0, 3'b111, 2'b11);
	
	di_0	=	$random;//16'h00_00;
	di_1	=	$random;//16'h00_00;
	di_2	=	$random;//16'h00_00;
	di_3	=	$random;//16'h00_00;
	fork begin
		for(int i = 0; i < 50; i++) begin
			@(negedge SystemClock);
			di_0	+=	 1;
			di_1	+=	 1;
			di_2	+=	 1;
			di_3	+=	 1;
		end
	end
	begin
		delay_val	=	3'd0;
		move_tap(1'b0, delay_val, 2'b00);
		forked_0_drop = 1'b1;
		move_tap(1'b0, delay_val, 2'b01);
		forked_1_drop = 1'b1;
		move_tap(1'b0, delay_val, 2'b10);
		forked_2_drop = 1'b1;
		move_tap(1'b0, delay_val, 2'b11);
		forked_3_drop = 1'b1;
	end
	
	join
	forked_0_drop = 1'b0;
	forked_1_drop = 1'b0;
	forked_2_drop = 1'b0;
	forked_3_drop = 1'b0;

	repeat(10) @(posedge SystemClock);

	/* Now we choose a different delay tap for
	* each line, reprogram, and check whether 
	* the number of repeated packets matches the 
	* expected number given the delay for each 
	* line. All lines start with delay of 7 and 
	* transition to a different value.
	* **NOTE**: We DO NOT change the delay tap
	* for line 3 but WE DO reprogram it. There
	* should be no dropped packets in this case.*/
	reset_all();
	// Programming the taps to 7
	move_tap(1'b0, 3'b111, 2'b00);
	move_tap(1'b0, 3'b111, 2'b01);
	move_tap(1'b0, 3'b111, 2'b10);
	move_tap(1'b0, 3'b000, 2'b11);
	
	di_0	=	16'h00_00;
	di_1	=	16'h00_00;
	di_2	=	16'h00_00;
	di_3	=	16'h00_00;
	fork begin
		for(int i = 0; i < 50; i++) begin
			@(negedge SystemClock);
			di_0	+=	 1;
			di_1	+=	 1;
			di_2	+=	 1;
			di_3	+=	 1;
		end
	end
	begin
		move_tap(1'b0, 3'd4, 2'b00);
		forked_0_tap_4 = 1'b1;
		move_tap(1'b0, 3'd2, 2'b01);
		forked_1_tap_4 = 1'b1;
		move_tap(1'b0, 3'd6, 2'b10);
		forked_2_tap_4 = 1'b1;
		move_tap(1'b0, 3'd0, 2'b11);
		forked_3_tap_4 = 1'b1;
	end
	
	join
	forked_0_tap_4 = 1'b0;
	forked_1_tap_4 = 1'b0;
	forked_2_tap_4 = 1'b0;
	forked_3_tap_4 = 1'b0;

	//-------------------------
	// Testing err_ signal 
	//-------------------------
	// Try programming in read mode and 
	// check to see if err_ signal is asserted
	reset_all();
	move_tap(1'b1, 3'b010, 2'b00);

	/* Deassert prgrm_go_ prematurely and
	* see if err_ is asserted*/
	reset_all();
    @(negedge SystemClock);
    prgrm_go_	=	1'b0;
    prgrm_in	=	1'b0;
    @(negedge SystemClock);
    prgrm_in	=	1'b0;
    @(negedge SystemClock);
    prgrm_in	=	1'b0;
	// Deasserting prgrm_go_ - err_ should be asserted
	prgrm_go_	=	1'b1;
    @(negedge SystemClock);
    prgrm_in	=	1'b1;
    @(negedge SystemClock);
    prgrm_in	=	1'b1;
    @(negedge SystemClock);
    prgrm_in	=	1'b1;
    @(negedge SystemClock);
    prgrm_go_	=	1'b1;
	prgrm_in	=	1'b0;

	reset_all();
	//Terminate Simulation
    #50000 $finish;
  end
  
  //initial begin
  //  $dumpfile("./obj/verilog.dump");
  //  $dumpvars(0,audio_app_test_top);
  //end

  //
  // CREATE YOUR TESTBENCH BELOW
  //

  //--------------------------------
  //	 CONCURRENT ASSERTIONS
  //--------------------------------
  
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
  /* Checking that only 7 words are repeated*/
  move_tap_0_7_0: assert property (@(negedge SystemClock) 
  										disable iff (!SystemReset_) (forked_0 |-> (do_0 == $past(di_0, 7))));
  move_tap_0_7_1: assert property (@(negedge SystemClock) 
  										disable iff (!SystemReset_) (forked_1 |-> (do_1 == $past(di_1, 7))));
  move_tap_0_7_2: assert property (@(negedge SystemClock) 
  										disable iff (!SystemReset_) (forked_2 |-> (do_2 == $past(di_2, 7))));
  move_tap_0_7_3: assert property (@(negedge SystemClock) 
  										disable iff (!SystemReset_) (forked_3 |-> (do_3 == $past(di_3, 7))));
  /* Checking that no more than 7 words are dropped*/
  move_tap_7_0_0: assert property (@(negedge SystemClock) 
  		     						disable iff (!SystemReset_) (forked_0_drop |-> (do_0 == di_0)));
  move_tap_7_0_1: assert property (@(negedge SystemClock) 
  		     						disable iff (!SystemReset_) (forked_1_drop |-> ((do_1 - $past(do_1)) == 8)||(do_1 == di_1)));
  move_tap_7_0_2: assert property (@(negedge SystemClock) 
  		     						disable iff (!SystemReset_) (forked_2_drop |-> ((do_2 - $past(do_2)) == 8)||(do_2 == di_2)));
  move_tap_7_0_3: assert property (@(negedge SystemClock) 
  									disable iff (!SystemReset_) (forked_3_drop |-> ((do_3 - $past(do_3)) == 8)||(do_3 == di_3)));

  /* Checking that the number of packets dropped when delay
  * tap is reprogrammed to 4 from 7 is 3. We do this by taking 
  * the difference between the output value for each delay line 
  * at every cycle after reprogramming and making sure that 
  * the value is 4 (since the inputs are increasing by a value 
  * of 1 every cycle and 3 words are dropped due to reprogramming)*/
  move_tap_0_7_4: assert property (@(negedge SystemClock) 
  			 			disable iff (!SystemReset_) (forked_0_tap_4 |-> (do_0 == di_0 - 16'd4)));
  move_tap_1_7_4: assert property (@(negedge SystemClock) 
  			 			disable iff (!SystemReset_) (forked_1_tap_4 |-> (do_1 == di_1 - 16'd2)));
  move_tap_2_7_4: assert property (@(negedge SystemClock) 
  			 			disable iff (!SystemReset_) (forked_2_tap_4 |-> (do_2 == di_2 - 16'd6)));
  move_tap_3_7_4: assert property (@(negedge SystemClock) 
  						disable iff (!SystemReset_) (forked_3_tap_4 |-> (do_3 == do_3)));



endmodule
