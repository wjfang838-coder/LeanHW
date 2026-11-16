module signed_div_const (
  input wire signed [3:0] a,
  output wire signed [3:0] q,
  output wire signed [3:0] r
);
  assign q = a / -4'sd3;
  assign r = a % -4'sd3;
endmodule
