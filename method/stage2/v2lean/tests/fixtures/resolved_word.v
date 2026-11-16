module resolved_word(inout [1:0] data, input [1:0] a,b, input ea,eb, output [1:0] observed);
  wire [1:0] merged;
  assign merged = ea ? a : 2'bzz;
  assign merged = eb ? b : 2'bzz;
  assign data = merged;
  assign observed = data;
endmodule
