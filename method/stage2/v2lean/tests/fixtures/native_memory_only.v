module native_memory_only (
  input clk, input we, input wa, input ra,
  input [7:0] data, output [7:0] q
);
  reg [7:0] mem [0:1];
  always @(posedge clk) if (we) mem[wa] <= data;
  assign q = mem[ra];
endmodule
