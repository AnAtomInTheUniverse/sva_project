`timescale 1ns/1ns
`define CLOCK_PERIOD 10

module test_arbiter;

  reg clock;
  reg reset;

  reg [1:0] request;
  wire [1:0] grant;

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
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    @(posedge clock);
    reset = 1'b0;

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
  always @(posedge clock) begin
    request = $random;
  end

  ////////////////////////////////////////////////////////////////////
  // assertions
  ////////////////////////////////////////////////////////////////////

  prop_reset: assert property (@(posedge clock) reset |-> ##1 grant == 2'b00);

  //
  // FIXME: CREATE YOUR ASSERTIONS BELOW
  //

endmodule
