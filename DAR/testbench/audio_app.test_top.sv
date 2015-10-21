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
	

	// Reset Signal Testing
	// Feed in non-zero values to each delay line
	// Set delay to 7 and then assert reset - Make
	// sure that all of the outputs are 0 after 
	// after reset asserts
	@(posedge SystemClock);
	di_0	=	16'h00_11;
	di_1	=	16'h00_22;
	di_2	=	16'h00_44;
	di_3	=	16'h00_88;
	for(int i = 0; i < 4; i++) begin
		@(posedge SystemClock);
		prgrm_go_	=	1'b0;
		prgrm_in	=	1'b0;
		@(posedge SystemClock);
		prgrm_in	=	(i%2) ? 1'b1: 1'b0;
		@(posedge SystemClock);
		prgrm_in	=	(i/2) ? 1'b1: 1'b0;
		@(posedge SystemClock);
		prgrm_in	=	1'b1;
		@(posedge SystemClock);
		prgrm_in	=	1'b1;
		@(posedge SystemClock);
		prgrm_in	=	1'b1;
		@(posedge SystemClock);
		prgrm_go_	=	1'b1;
	end


	repeat(6) @(posedge SystemClock);
	SystemReset_	=	1'b0;

	repeat(2) @(posedge SystemClock);
	SystemReset_	=	1'b1;
    // terminate simulation
    // FIXME: change simulation time if necessary
    #1000000 $finish;
  end
  
  //initial begin
  //  $dumpfile("./obj/verilog.dump");
  //  $dumpvars(0,audio_app_test_top);
  //end

  //
  // CREATE YOUR TESTBENCH BELOW
  //

  //-------------------------------------
  //		 ASSERTIONS
  //-------------------------------------
  
  //----------
  //Reset Assertions
  //----------
   prop_assert_rst_: assert property (@(posedge SystemClock) (SystemReset_ ##1 !SystemReset_) |=> (do_0 == 16'h0000) && (do_1 == 16'h0000) && (do_2 == 16'h0000) && (do_3 == 16'h0000));

  //----------
  //Err Signal Assertions
  //----------
  // prgrm_go cannot be deasserted (1'b1) during the 6 cycles of delay programming
  prop_prgrm_go_deasserted: assert property (@(posedge SystemClock) disable iff (!SystemReset_) ((prgrm_go_ ##1 !prgrm_go_) ##[1:5] prgrm_go_ )|=> !err_);
  // err_ should assert (1'b0) if bit0 of prgrm_in is 1 during programming 
  // since Read mode is not supported by design
  prop_prgrm_rd_err: assert property (@(posedge SystemClock) disable iff (!SystemReset_) (err_ && prgrm_go_) ##1 (!prgrm_go_ && prgrm_in) |=> !err_);

  //----------




endmodule
