// Formal-only independent transaction ISA. Its RAM is related to the DUT's
// arbitrary initial RAM by the single initial-state assumption, then updated
// only by the reference instruction semantics. No DUT decode/ALU is called.
`include "isa_reference.svh"
reg [31:0] reference_regs [0:31];
reg [31:0] reference_ram [0:255];
reg [31:0] reference_pc;
reg [2:0] reference_fault;
wire [255:0] initial_word_equal;
genvar memory_word_index;
generate
    for (memory_word_index=0;memory_word_index<256;memory_word_index=memory_word_index+1) begin: initial_memory_relation
        assign initial_word_equal[memory_word_index] = ram[memory_word_index] == reference_ram[memory_word_index];
    end
endgenerate
wire formal_ram_init_equal = (`PROPERTY==0 || `PROPERTY==1) ? &initial_word_equal : 1'b1;
wire [31:0] reference_a = retire_insn[19:15] == 0 ? 0 : reference_regs[retire_insn[19:15]];
wire [31:0] reference_b = retire_insn[24:20] == 0 ? 0 : reference_regs[retire_insn[24:20]];
wire ref_load = retire_insn[6:0] == 7'h03;
wire ref_store = retire_insn[6:0] == 7'h23;
wire ref_fence = retire_insn[6:0] == 7'h0f;
wire [31:0] ref_immediate = ref_store ?
    {{20{retire_insn[31]}},retire_insn[31:25],retire_insn[11:7]} :
    {{20{retire_insn[31]}},retire_insn[31:20]};
wire [31:0] ref_address = reference_a+ref_immediate;
wire [31:0] ref_mem_word = reference_ram[ref_address[9:2]];
reg [31:0] ref_result,ref_mask,ref_data;
reg [2:0] ref_cause;
reg [31:0] ref_selected;
reg ref_misaligned;
always @* begin
    ref_result = reference_value(retire_insn,reference_a,reference_b,reference_pc);
    ref_selected = ref_mem_word >> (8*ref_address[1:0]);
    ref_mask=0;ref_data=0;ref_cause=0;ref_misaligned=0;
    if (ref_load || ref_store) begin
        case(retire_insn[14:12])
            1,5:ref_misaligned=ref_address[0];
            2:ref_misaligned=|ref_address[1:0];
            default:ref_misaligned=0;
        endcase
        if(ref_misaligned) ref_cause=ref_store?2:1;
        else if(ref_address>=1024) ref_cause=ref_store?4:3;
        if(ref_load) begin
            case(retire_insn[14:12])
                0:ref_result={{24{ref_selected[7]}},ref_selected[7:0]};
                1:ref_result={{16{ref_selected[15]}},ref_selected[15:0]};
                2:ref_result=ref_mem_word;
                4:ref_result={24'b0,ref_selected[7:0]};
                5:ref_result={16'b0,ref_selected[15:0]};
                default:ref_result=0;
            endcase
        end else begin
            ref_result=0;
            case(retire_insn[14:12])
                0:ref_mask=32'hff << (8*ref_address[1:0]);
                1:ref_mask=32'hffff << (8*ref_address[1:0]);
                2:ref_mask=32'hffffffff;
                default:ref_mask=0;
            endcase
            ref_data=reference_b << (8*ref_address[1:0]);
        end
        if(ref_cause!=0) ref_result=0;
    end
    if(ref_fence) ref_result=0;
end
reg [159:0] accepted_queue,next_accepted_queue;
reg [2:0] accepted_count,next_accepted_count;
always @* begin
    next_accepted_queue=accepted_queue;next_accepted_count=accepted_count;
    if(retire_valid) begin
        next_accepted_queue=accepted_queue>>32;
        next_accepted_count=accepted_count-1;
    end
    if(insn_valid&&insn_ready) begin
        next_accepted_queue[32*next_accepted_count +:32]=insn;
        next_accepted_count=next_accepted_count+1;
    end
    if(trap_valid) begin next_accepted_queue=0;next_accepted_count=0;end
end
integer ref_register_index;
always @(posedge clk) begin
    if(rst) begin
        reference_pc<=0;reference_fault<=0;
        for(ref_register_index=0;ref_register_index<32;ref_register_index=ref_register_index+1)
            reference_regs[ref_register_index] <= ref_register_index==0 ? 0 : reg_init[32*ref_register_index +:32];
        accepted_queue<=0;accepted_count<=0;
    end else if(formal_past_valid) begin
        if(`PROPERTY==0 || `PROPERTY==1) begin
            assert(arch_pc==reference_pc);
            assert(fault_cause==reference_fault);
            assert(debug_reg_data==(debug_reg_addr==0 ? 0 : reference_regs[debug_reg_addr]));
            assert(debug_mem_data==reference_ram[debug_mem_addr]);
            if(retire_valid) begin
                assert(retire_pc==reference_pc);
                assert(retire_value==ref_result);
                assert(retire_rd==((ref_store||ref_fence||ref_cause!=0)?5'b0:retire_insn[11:7]));
                assert(trap_valid==(ref_cause!=0));
                assert(trap_cause==ref_cause);
                assert(retire_store==(ref_store&&ref_cause==0));
                if(ref_load||ref_store) assert(retire_address==ref_address);
                if(retire_store) begin
                    assert(retire_store_data==ref_data);
                    assert(retire_store_mask==ref_mask);
                end
            end
        end
        if(`PROPERTY==0 || `PROPERTY==2) begin
            assert(accepted_count<=5);
            if(retire_valid) begin assert(accepted_count!=0);assert(retire_insn==accepted_queue[31:0]);end
        end
        if(retire_valid) begin
            if(ref_cause!=0) reference_fault<=ref_cause;
            else begin
                reference_pc<=reference_pc+4;
                if(!ref_store&&!ref_fence&&retire_insn[11:7]!=0) reference_regs[retire_insn[11:7]]<=ref_result;
                if(ref_store) reference_ram[ref_address[9:2]] <= (ref_mem_word&~ref_mask)|(ref_data&ref_mask);
            end
        end
        accepted_queue<=next_accepted_queue;accepted_count<=next_accepted_count;
    end
end
