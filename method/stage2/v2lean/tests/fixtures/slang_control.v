module slang_control(
 input signed [1:0] a,
 input [2:0] b,
 input s,
 output [3:0] mixed_sum, signed_ext, zero_ext,
 output mixed_lt, signed_lt, same,
 output [1:0] ternary,
 output reg [1:0] procedural, sequential_assign
);
 reg [1:0] temp;
 assign mixed_sum = a + b;
 assign mixed_lt = a < b;
 assign signed_lt = $signed(a) < $signed(b);
 assign signed_ext = a;
 assign zero_ext = $unsigned(a);
 assign same = a === b[1:0];
 assign ternary = s ? a : b[1:0];
 always @* begin
   if (s) procedural = a; else procedural = b[1:0];
   temp = a;
   temp = temp + 1'b1;
   sequential_assign = temp ^ b[1:0];
 end
endmodule
