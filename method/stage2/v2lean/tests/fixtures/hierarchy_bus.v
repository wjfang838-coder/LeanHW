module leaf #(parameter W=1)(input clk, input reset_n, input [W-1:0] d, output reg [W-1:0] q);
  always @(posedge clk or negedge reset_n)
    if (!reset_n) q <= 0; else q <= d;
endmodule
module wrap #(parameter W=1)(input clk, input reset_n, input [W-1:0] d, output [W-1:0] q);
  leaf #(.W(W)) inner(.clk(clk),.reset_n(reset_n),.d(d),.q(q));
endmodule
module hierarchy_bus(input clk, input reset_n, input [1:0] d0, input [1:0] d1,
                     input ea, input eb, input select_a, inout [1:0] bus, output reg [1:0] observed);
  wire [1:0] a,b;
  wrap #(.W(2)) first(.clk(clk),.reset_n(reset_n),.d(d0),.q(a));
  leaf #(.W(2)) second(.clk(clk),.reset_n(reset_n),.d(d1),.q(b));
  assign bus=ea ? a : 2'bz;
  assign bus=eb ? b : 2'bz;
  always @* begin
    observed=bus;
    if (select_a) observed=a;
  end
endmodule
