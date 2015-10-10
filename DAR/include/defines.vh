`ifdef DEFINES
`else
`define DEFINES              1
`define PCM                 16
`define D_DEPTH              3    // delay depth is 2^DEPTH
`define IDLE            3'b000
`define WRITE_SELECT    3'b001
`define WRITE_DELAY     3'b011
`define READ            3'b111
`define ERROR           3'b110
`endif


