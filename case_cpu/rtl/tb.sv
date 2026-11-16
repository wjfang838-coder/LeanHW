module tb;
  reg clk=0,rst,valid;
  reg [1023:0] reg_init;
  reg [31:0] insn;
  reg [4:0] stalls,dbg;
  wire ready,retired;
  wire [31:0] ri,rpc,rv,debug_data,pc;
  wire [4:0] rd,occ;
  case_cpu dut(clk,rst,reg_init,insn,valid,
    stalls[0],stalls[1],stalls[2],stalls[3],stalls[4],ready,
    retired,ri,rpc,rv,rd,dbg,debug_data,pc,occ);
  integer inf,outf,r,j,rr,vv,ss,dd;
  reg [31:0] ww,seed;
  reg [4095:0] inpath,outpath;
  initial begin
    if(!$value$plusargs("input=%s",inpath)) $fatal(1,"missing input");
    if(!$value$plusargs("output=%s",outpath)) $fatal(1,"missing output");
    inf=$fopen(inpath,"r"); outf=$fopen(outpath,"w");
    if(!inf || !outf) $fatal(1,"cannot open trace");
    while(!$feof(inf)) begin
      r=$fscanf(inf,"%d %d %d %d %d",rr,vv,ww,ss,dd);
      if(r==5) begin
        for(j=0;j<32;j=j+1) begin
          r=$fscanf(inf,"%d",seed);
          if(r!=1) $fatal(1,"bad register seed");
          reg_init[32*j +:32]=seed;
        end
        rst=rr; valid=vv; insn=ww; stalls=ss; dbg=dd;
        #1;
        $fdisplay(outf,"%0d %0d %0d %0d %0d %0d %0d %0d %0d",
          ready&&valid,retired,ri,rpc,rv,rd,rst?0:pc,rst?0:debug_data,rst?0:occ);
        clk=1; #1; clk=0;
      end else if(!$feof(inf)) $fatal(1,"bad input row");
    end
    $fclose(inf); $fclose(outf); $finish;
  end
endmodule
