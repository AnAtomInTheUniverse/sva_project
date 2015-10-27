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
    repeat(9) @(posedge clock);
    reset = 1'b0;

    // Carrying out directed tests with known input requests
    // Baseline condition is when there are no requests
    // In this case the arbiter could keep granting to
    // just one of the outputs, or alternate between 0 and 1
    request     = 'b0;
    last_req    = 'b0;  
	repeat(2) @(posedge clock);

    @(negedge clock) $display("---------- Both Requests Deasserted ----------");
    // See output grant for 6 cycles
    repeat(6) @(posedge clock)
    
    // Check the condition when only request[0] is asserted
    // for multiple cycles
    request     = 'b01;

    @(negedge clock) $display("---------- One Request Asserted ----------");
    // See output grant for 6 cycles
    for(int j = 0; j < 6; j++) begin
        $display("grant = %b", grant);
        @(posedge clock);
    end

    // In this section we alternate between the two requests
    // with each one being high for 2 cycles. We want to check
    // if the arbiter correctly grants to only the signal that
    // is requesting and not to the other
    last_req    = 2'b01;
    $display("---------- Alternating Requests ----------");
    for(int i = 0; i < 10; i++) begin
       request  = last_req;
       repeat(2) @(posedge clock) ;
       last_req =   {~request[1], ~request[0]};
    end

    // In this portion of the test we randomize the request
    // vector and check the corresponding grants
    $display("---------- Randomizing Requests ----------");
    for(int i = 0; i < 20; i++) begin
        request = $random;
        repeat(2) @(posedge clock) ;
    end

    // In this section both of the request inputs are asserted
    // The arbiter must fairly grant to both requests, one at a time
    $display("---------- Both Requests Asserted ----------");
    request = 2'b11;
    repeat(20) @(posedge clock) $display("grant = %b", grant);
	
	// Randomizing for the remaining cycles
	repeat(500) @(posedge clock) request = $random;
    // terminate simulation
    // FIXME: change simulation time if necessary
    #1000 $finish;
  end

  always begin
    #(`CLOCK_PERIOD/2.0);
    clock = ~clock;
  end

  always @(negedge clock) begin
		  $display("grant = %d", grant);
  end
  ////////////////////////////////////////////////////////////////////
  // request signal generation
  ////////////////////////////////////////////////////////////////////
  //
  // The below always statement generates a random number every cycle and
  // assign the number to request.
  //
  //always @(posedge clock) begin
  //  request = $random;
  //end

  ////////////////////////////////////////////////////////////////////
  // assertions
  ////////////////////////////////////////////////////////////////////

  prop_reset: assert property (@(posedge clock) reset |-> ##1 grant == 2'b00);

  //
  // FIXME: CREATE YOUR ASSERTIONS BELOW
  //

  // Only one of the two requests can be granted at a time - both
  // bits of grant[1:0] cannot be asserted simultaneously (mutual exclusion)
  prop_mutex: assert property (@(posedge clock) disable iff (reset) !(grant[0] && grant[1]));

  // If request[0] is asserted and request[1] is not, then the 
  // arbiter must grant to 0 in the next cycle
  prop_gnt_0: assert property (@(posedge clock) disable iff (reset) (!request[1] && request[0]) |-> ##1 grant == 2'b01);

  // If request[1] is asserted and request[0] is not, then the 
  // arbiter must grant to 1 in the next cycle
  prop_gnt_1: assert property (@(posedge clock) disable iff (reset) (request[1] && ~request[0]) |-> ##1 grant == 2'b10);

  // Test fairness: if both requests are asserted for an extended 
  // number of cycles, then the arbiter must grant to both fairly
  // by alternating between the two
  prop_fair: assert property (@(posedge clock) disable iff (reset)  (grant[0]) && (request == 2'b11) |=> grant[1]);

  // The arbiter should not grant incorrectly - if an input is not requesting, 
  // then the arbiter should not grant that request line
  prop_correct0: assert property (@(posedge clock) disable iff (reset) (!request[0] |=> grant[0] != 1));
  prop_correct1: assert property (@(posedge clock) disable iff (reset) (!request[1] |=> grant[1] != 1));

endmodule
