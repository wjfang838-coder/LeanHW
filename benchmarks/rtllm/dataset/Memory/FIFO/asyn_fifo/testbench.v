`timescale 1ns/1ns
// Local benchmark repair: one stimulus driver and an independent FIFO queue.
// The shipped static vectors were produced by a reference that overfills DEPTH.
module asyn_fifo_tb;
  reg wclk=0,rclk=0,wrstn=1,rrstn=1,winc=0,rinc=0;
  reg [7:0] wdata=0;
  wire wfull,rempty;
  wire [7:0] rdata;
  reg [7:0] queue [0:63];
  reg [7:0] expected;
  integer writes=0,reads=0,errors=0,i;
  asyn_fifo #(.WIDTH(8),.DEPTH(16)) dut(
    .wclk(wclk),.rclk(rclk),.wrstn(wrstn),.rrstn(rrstn),
    .winc(winc),.rinc(rinc),.wdata(wdata),
    .wfull(wfull),.rempty(rempty),.rdata(rdata));
  always #5 wclk=~wclk;
  always #10 rclk=~rclk;
  always @(posedge wclk) begin
    if(wrstn && winc && wfull===1'b0) begin
      if(writes-reads>=16) begin errors=errors+1; $display("Overflow at %0t",$time); end
      queue[writes]=wdata;
      writes=writes+1;
    end
  end
  always @(posedge rclk) begin
    if(rrstn && rinc && rempty===1'b0) begin
      if(reads>=writes) begin errors=errors+1; $display("Underflow at %0t",$time); end
      expected=queue[reads];
      reads=reads+1;
      #1;
      if(rdata!==expected) begin
        errors=errors+1;
        $display("Data mismatch expected=%h got=%h",expected,rdata);
      end
    end
  end
  initial begin
    #1; wrstn=0; rrstn=0;
    repeat(4) @(negedge wclk);
    wrstn=1; rrstn=1;
    @(negedge wclk); winc=1;
    for(i=0;i<20;i=i+1) begin
      wdata=8'h40+i;
      @(negedge wclk);
    end
    winc=0;
    #1;
    if(writes!=16 || wfull!==1'b1) errors=errors+1;
    repeat(8) @(negedge rclk);
    if(rempty!==1'b0) errors=errors+1;
    rinc=1;
    repeat(20) @(negedge rclk);
    rinc=0;
    repeat(8) @(negedge rclk);
    if(reads!=16 || rempty!==1'b1) errors=errors+1;
    if(errors==0) $display("===========Your Design Passed===========");
    else $display("===========Test completed with %0d failures===========",errors);
    $display("QUEUE writes=%0d reads=%0d errors=%0d",writes,reads,errors);
    $finish;
  end
endmodule
