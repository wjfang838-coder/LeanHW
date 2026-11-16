module fourstate_ops(
  input [1:0] a, b,
  input s,
  output [1:0] inv, band, bor, bxor, add, sub, mul, shl, shr, sshr, choice,
  output eq, lt, slt, truth,
  output [3:0] sext,
  output reg [1:0] selected
);
assign inv = ~a;
assign band = a & b;
assign bor = a | b;
assign bxor = a ^ b;
assign add = a + b;
assign sub = a - b;
assign mul = a * b;
assign shl = a << b;
assign shr = a >> b;
assign sshr = $signed(a) >>> b;
assign choice = s ? a : b;
assign eq = a == b;
assign lt = a < b;
assign slt = $signed(a) < $signed(b);
assign truth = |a;
assign sext = {{2{a[1]}}, a};
always @* begin
  case (a)
    2'b00: selected = b;
    2'b01: selected = 2'bz;
    default: selected = 2'bx;
  endcase
end
endmodule
