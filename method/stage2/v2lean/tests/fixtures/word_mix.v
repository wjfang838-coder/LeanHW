module word_mix (
    input [7:0] a,
    input [7:0] b,
    input sel,
    output [7:0] y,
    output carry
);
    wire [8:0] sum = {1'b0, a} + {1'b0, b};
    wire [7:0] mixed = a ^ {b[3:0], b[7:4]};
    assign y = sel ? sum[7:0] : mixed;
    assign carry = sum[8];
endmodule
