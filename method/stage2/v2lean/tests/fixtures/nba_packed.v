module nba_packed(input clk, input reset_n, input signed [3:0] index,
                  input [2:0] d, output reg [7:0] q, output [2:0] observed);
  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) q <= 8'h5a;
    else begin
      q[index +: 3] <= d;
      q[index+1 +: 2] <= d[2:1];
    end
  end
  assign observed = q[index +: 3];
endmodule
