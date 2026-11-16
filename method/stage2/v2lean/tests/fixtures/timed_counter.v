`timescale 10ns / 100ps
module timed_counter(output reg [3:0] count);
  initial count = 4'd0;
  always #3 count = count + 4'd1;
endmodule
