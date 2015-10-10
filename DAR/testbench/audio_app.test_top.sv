`timescale 1ns/1ns
module audio_app_test_top;
  parameter simulation_cycle = 100 ;
  
  reg  SystemClock ;
  reg  SystemReset_ ;
  wire  clk ;
  wire  rst_ ;
  wire  [15:0]  di_0 ;
  wire  [15:0]  di_1 ;
  wire  [15:0]  di_2 ;
  wire  [15:0]  di_3 ;
  wire  [15:0]  do_0 ;
  wire  [15:0]  do_1 ;
  wire  [15:0]  do_2 ;
  wire  [15:0]  do_3 ;
  wire  prgrm_in ;
  wire  prgrm_go_ ;
  wire  err_ ;
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
    SystemReset_ = 1'b0;
    @(posedge SystemClock);
    @(posedge SystemClock);
    @(posedge SystemClock);
    @(posedge SystemClock);
    @(posedge SystemClock);
    @(posedge SystemClock);
    @(posedge SystemClock);
    @(posedge SystemClock);
    @(posedge SystemClock);
    @(posedge SystemClock);
    SystemReset_ = 1'b1;

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
  
endmodule
