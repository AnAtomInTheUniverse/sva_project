`timescale 1ns/1ns
`define CLOCK_PERIOD 10

module test_arbiter;

  reg clock;
  reg reset;

  reg [1:0] request;
  wire [1:0] grant;

  // Local testbench variables
  bit[1:0]  rand_req;
  reg [1:0] last_req;
  ////////////////////////////////////////////////////////////////////
  // arbiter module instantiation
  ////////////////////////////////////////////////////////////////////
  arbiter arbiter_0 (.request(request), .grant(grant), .reset(reset), .clk(clock));

  ////////////////////////////////////////////////////////////////////
  // clock and reset generation
  ////////////////////////////////////////////////////////////////////
  initial begin
    clock = 1'b1;
    reset = 1'b1;

    // reset will be deasserted after 10 cycles
    repeat(10) @(posedge clock);
    /*@(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);*/
    reset = 1'b0;

    // Carrying out directed tests with known input requests
    // Baseline condition is when there are no requests
    // In this case the arbiter could keep granting to
    // just one of the outputs, or alternate between 0 and 1
    request     = 'b0;
    last_req    = 'b0;  

    $display("---------- Both Requests Deasserted ----------");
    // See output grant for 6 cycles
    for(int j = 0; j < 6; j++) begin
        $display("grant = %b", grant);
        @(posedge clk);
    end
    
    // Check the condition when only request[0] is asserted
    // for multiple cycles
    request     = 'b01;

    $display("---------- One Request Asserted ----------");
    // See output grant for 6 cycles
    for(int j = 0; j < 6; j++) begin
        $display("grant = %b", grant);
        @(posedge clk);
    end

    // In this section we alternate between the two requests
    // with each one being high for 2 cycles. We want to check
    // if the arbiter correctly grants to only the signal that
    // is requesting and not to the other
    last_req    = 2'b01;
    $display("---------- Alternating Requests ----------");
    for(int i = 0; i < 10; i++) begin
       request  = last_req;
       repeat(2) @(posedge clk) ;
       assert 
       $display("grant = %b", grant);
       last_req =   {~request[1], ~request[0]};
    end

    // In this portion of the test we randomize the request
    // vector and check the corresponding grants
    $display("---------- Randomizing Requests ----------");
    for(int i = 0; i < 20; i++) begin
        request = std::randomize(rand_req);
        repeat(2) @(posedge clk) ;
        $display("grant = %b", grant);
    end

    // In this section both of the request inputs are asserted
    // The arbiter must fairly grant to both requests, one at a time
    $display("---------- Both Requests Asserted ----------");
    request = 2'b11;
    repeat(20) @(posedge clk) $display("grant = %b", grant);
    // terminate simulation
    // FIXME: change simulation time if necessary
    #10000 $finish;
  end

  always begin
    #(`CLOCK_PERIOD/2.0);
    clock = ~clock;
  end

  ////////////////////////////////////////////////////////////////////
  // request signal generation
  ////////////////////////////////////////////////////////////////////
  //
  // The below always statement generates a random number every cycle and
  // assign the number to request.
  //
 // always @(posedge clock) begin
 //   request = $random;
 // end

  ////////////////////////////////////////////////////////////////////
  // assertions
  ////////////////////////////////////////////////////////////////////

  prop_reset: assert property (@(posedge clock) reset |-> ##1 grant == 2'b00);

  //
  // FIXME: CREATE YOUR ASSERTIONS BELOW
  //

  // Only one of the two requests can be granted at a time - both
  // bits of grant[1:0] cannot be asserted simultaneously
  prop_mutex: assert property (@(posedge clock) disable iff (reset) !(grant[0] == grant[1]));

  // If request[0] is asserted and request[1] is not, then the 
  // arbiter must grant to 0 in the next cycle
  prop_gnt_0: assert property (@(posedge clock) disable iff (reset) (~request[1] && request[0] |-> ##1 grant == 2'b01);

  // If request[1] is asserted and request[0] is not, then the 
  // arbiter must grant to 1 in the next cycle
  prop_gnt_1: assert property (@(posedge clock) disable iff (reset) (request[1] && ~request[1] |-> ##1 grant == 2'b10);
endmodule
