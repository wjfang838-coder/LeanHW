// Corrected FIFO reference: atomic binary/Gray position updates and registered
// next-state full/empty flags. Validate capacity independently of any candidate.
module asyn_fifo #(parameter WIDTH=8, DEPTH=16, ADDR_WIDTH=$clog2(DEPTH)) (
    input wclk,rclk,wrstn,rrstn,winc,rinc,
    input [WIDTH-1:0] wdata,
    output reg wfull,rempty,
    output [WIDTH-1:0] rdata
);
    reg [ADDR_WIDTH:0] wb,rb,wg,rg,rs1,rs2,ws1,ws2;
    wire push=wrstn && winc && !wfull;
    wire pop=rrstn && rinc && !rempty;
    wire [ADDR_WIDTH:0] wb1=wb+push, rb1=rb+pop;
    wire [ADDR_WIDTH:0] wg1=(wb1>>1)^wb1, rg1=(rb1>>1)^rb1;
    localparam [ADDR_WIDTH:0] FULL_MASK = ADDR_WIDTH == 0 ? 1 : (3 << (ADDR_WIDTH-1));
    wire full1=(wg1==(rs2 ^ FULL_MASK));
    wire empty1=(rg1==ws2);
    always @(posedge wclk or negedge wrstn) begin
        if(!wrstn) begin wb<=0; wg<=0; rs1<=0; rs2<=0; wfull<=0; end
        else begin wb<=wb1; wg<=wg1; rs1<=rg; rs2<=rs1; wfull<=full1; end
    end
    always @(posedge rclk or negedge rrstn) begin
        if(!rrstn) begin rb<=0; rg<=0; ws1<=0; ws2<=0; rempty<=1; end
        else begin rb<=rb1; rg<=rg1; ws1<=wg; ws2<=ws1; rempty<=empty1; end
    end
    dual_port_RAM #(.DEPTH(DEPTH),.WIDTH(WIDTH)) mem(
      .wclk(wclk),.wenc(push),.waddr(wb & ((1 << ADDR_WIDTH)-1)),.wdata(wdata),
      .rclk(rclk),.renc(pop),.raddr(rb & ((1 << ADDR_WIDTH)-1)),.rdata(rdata));
endmodule

module dual_port_RAM #(parameter DEPTH = 16,  parameter WIDTH = 8)
(
	 input wclk	,
	 input wenc	,
	 input [$clog2(DEPTH)-1:0] waddr  ,
	 input [WIDTH-1:0] wdata ,
	 input rclk	,
	 input renc	,
	 input [$clog2(DEPTH)-1:0] raddr ,
	 output reg [WIDTH-1:0] rdata 		
);

reg [WIDTH-1:0] RAM_MEM [0:DEPTH-1];

always @(posedge wclk) begin
	if(wenc)
		RAM_MEM[waddr] <= wdata;
end 

always @(posedge rclk) begin
	if(renc)
		rdata <= RAM_MEM[raddr];
end 

endmodule
