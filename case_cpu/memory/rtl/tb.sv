module tb;
    reg clk=0,rst=1;
    reg [1023:0] reg_init=0;
    reg [31:0] insn=0;
    reg insn_valid=0;
    reg [4:0] stalls=0;
    reg [3:0] memory_delay=0;
    reg [4:0] debug_reg_addr=0;
    reg [7:0] debug_mem_addr=0;
    reg [3:0] debug_counter_addr=0;
    wire [31:0] debug_counter_data;
    wire insn_ready,retire_valid,retire_store,trap_valid,halted;
    wire [31:0] retire_insn,retire_pc,retire_value,retire_address,retire_store_data,retire_store_mask;
    wire [31:0] arch_pc,debug_reg_data,debug_mem_data;
    wire [4:0] retire_rd,occupancy;
    wire [2:0] trap_cause,fault_cause;
    wire [7:0] stall_reason;
    case_cpu_memory dut(.*,
        .stall_fetch(stalls[0]),.stall_decode(stalls[1]),.stall_execute(stalls[2]),
        .stall_memory(stalls[3]),.stall_writeback(stalls[4]));
    string vectors,memory_file,trace_file;
    integer f,g,n,r,v,st,de,dr,dm,dc;
    initial begin
        if (!$value$plusargs("VECTORS=%s",vectors)) $fatal;
        if (!$value$plusargs("MEM=%s",memory_file)) $fatal;
        if (!$value$plusargs("TRACE=%s",trace_file)) $fatal;
        $readmemh(memory_file,dut.ram);
        #5;clk=1;#5;clk=0;
        f=$fopen(vectors,"r");g=$fopen(trace_file,"w");
        while (!$feof(f)) begin
            n=$fscanf(f,"%d %d %h %d %d %d %d %d %h\n",r,v,insn,st,de,dr,dm,dc,reg_init);
            if (n==9) begin
                rst=r;insn_valid=v;stalls=st;memory_delay=de;
                debug_reg_addr=dr;debug_mem_addr=dm;debug_counter_addr=dc;
                #5;
                $fdisplay(g,"%0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d",
                    insn_valid&&insn_ready,retire_valid,retire_insn,retire_pc,retire_rd,retire_value,
                    retire_store,retire_address,retire_store_data,retire_store_mask,trap_valid,trap_cause,
                    arch_pc,halted,fault_cause,debug_reg_data,debug_mem_data,occupancy,debug_counter_data);
                #5;clk=1;#5;clk=0;
            end
        end
        $fclose(f);$fclose(g);$finish;
    end
endmodule
