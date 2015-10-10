module arbiter ( request, grant, reset, clk ) ;
  input [1:0] request ;
  output [1:0] grant ;
  input  reset ;
  input  clk ;
  wire  winner ;
  reg last_winner ;
  reg [1:0] grant ;
  wire [1:0] next_grant ;
  
  assign next_grant[0] 
    = ~reset &( request[0] & 
              (~request[1] | last_winner) ) ;
  assign next_grant[1]
    = ~reset & ( request[1] &
              (~request[0] | last_winner) ) ;

  assign winner 
    = ~reset &  ~next_grant[0] & 
              ( last_winner | next_grant[1] ) ;

  always @(posedge clk) begin
    last_winner = winner ;
    grant = next_grant ;
  end

endmodule
