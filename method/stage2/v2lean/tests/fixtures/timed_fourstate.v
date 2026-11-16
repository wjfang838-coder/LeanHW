`timescale 1ps / 1fs
module timed_fourstate(output reg [3:0] q);
  initial q = 4'b01xz;
  always #2 q = ~q;
endmodule
