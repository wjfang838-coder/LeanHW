`ifndef PROPERTY
`define PROPERTY 0
`endif
module miter(input wire clk, rst, input wire [1023:0] reg_init,
  input wire [31:0] insn, input wire insn_valid,
  input wire [4:0] stalls, debug_addr);
  wire ready,retired;
  wire [31:0] ri,rpc,rv,debug_data,pc;
  wire [4:0] rd,occupancy;
  wire [4:0] dut_debug_addr=(`PROPERTY==3) ? 5'b0 : debug_addr;
  case_cpu dut(clk,rst,reg_init,insn,insn_valid,
    stalls[0],stalls[1],stalls[2],stalls[3],stalls[4],ready,
    retired,ri,rpc,rv,rd,dut_debug_addr,debug_data,pc,occupancy);
  `include "isa_reference.svh"
  reg started=0;
  reg [1023:0] reference_regs;
  reg [31:0] reference_pc;
  wire [31:0] ra=(ri[19:15]==0) ? 0 : reference_regs[32*ri[19:15] +:32];
  wire [31:0] rb=(ri[24:20]==0) ? 0 : reference_regs[32*ri[24:20] +:32];
  wire [31:0] expected=reference_value(ri,ra,rb,reference_pc);
  reg [159:0] queue,n_queue;
  reg [2:0] count,n_count;
  always @* begin
    n_queue=queue; n_count=count;
    if(retired) begin n_queue=queue>>32; n_count=count-1; end
    if(insn_valid && ready) begin n_queue[32*n_count +:32]=insn; n_count=n_count+1; end
  end
  always @(posedge clk) begin
    started<=1;
    if(!started) assume(rst);
    if(rst) begin
      reference_regs<={reg_init[1023:32],32'b0}; reference_pc<=0;
      queue<=0; count<=0;
    end else if(started) begin
      // PROPERTY=0: complete safety miter; 1: architectural refinement;
      // 2: acceptance/order; 3: small interface sanity check.
      if (`PROPERTY==0 || `PROPERTY==1) begin
        assert(pc==reference_pc);
        assert(debug_data==((debug_addr==0) ? 0 : reference_regs[32*debug_addr +:32]));
        if(retired) begin assert(rv==expected); assert(rpc==reference_pc); assert(rd==ri[11:7]); end
      end
      if (`PROPERTY==0 || `PROPERTY==2) begin
        assert(count<=5);
        if(retired) begin assert(count!=0); assert(ri==queue[31:0]); end
      end
      if (`PROPERTY==0 || `PROPERTY==3) begin
        assert(!retired || !stalls[4]);
        assert(debug_addr!=0 || debug_data==0);
        assert(!ready || !stalls[0]);
      end
      if(retired) begin
        if(rd!=0) reference_regs[32*rd +:32]<=expected;
        reference_pc<=reference_pc+4;
      end
      queue<=n_queue; count<=n_count;
    end
  end
endmodule
