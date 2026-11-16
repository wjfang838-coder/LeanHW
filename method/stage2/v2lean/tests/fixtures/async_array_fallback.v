module async_array_fallback(input clk, input rst, input en, input addr,
  input [7:0] d, output [7:0] q);
  reg [7:0] mem [0:1];
  always @(posedge clk or posedge rst) begin
    if (rst) begin mem[0] <= 8'h00; mem[1] <= 8'h00; end
    else if (en) mem[addr] <= d;
  end
  assign q = mem[addr];
endmodule
