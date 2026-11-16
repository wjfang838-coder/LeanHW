module nba_overlap(input clk, input reset_n, input en, input [3:0] d,
                   output reg [3:0] a, output reg [3:0] b);
  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin a <= 0; b <= 1; end
    else begin
      a <= b;
      b <= a;
      a[1:0] <= d[1:0];
      if (en) a[2:1] <= d[3:2];
      b <= a + 1'b1;
    end
  end
endmodule
