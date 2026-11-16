module guarded_slice (
  input wire [1:0] data,
  input wire [1:0] index,
  output wire value
);
  assign value = index < 2 ? data[index] : 1'b0;
endmodule
