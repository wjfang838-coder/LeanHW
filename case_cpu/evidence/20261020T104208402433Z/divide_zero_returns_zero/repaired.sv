// RV32 arithmetic subset. No instruction/data memory, branch, CSR, or trap unit.
// All state changes on the rising edge; reset overrides every other action.
module case_cpu (
  input wire clk, input wire rst,
  input wire [1023:0] reg_init,
  input wire [31:0] insn, input wire insn_valid,
  input wire stall_fetch, stall_decode, stall_execute, stall_memory, stall_writeback,
  output reg insn_ready,
  output wire retire_valid, output wire [31:0] retire_insn,
  output wire [31:0] retire_pc, retire_value,
  output wire [4:0] retire_rd,
  input wire [4:0] debug_addr, output wire [31:0] debug_data,
  output wire [31:0] arch_pc, output wire [4:0] occupancy
);
  localparam ADD=0, SUB=1, SLL=2, SLT=3, SLTU=4, XOR_=5, SRL=6,
    SRA=7, OR_=8, AND_=9, ADDI=10, SLTI=11, SLTIU=12, XORI=13,
    ORI=14, ANDI=15, SLLI=16, SRLI=17, SRAI=18, LUI=19, AUIPC=20,
    MUL=21, MULH=22, MULHSU=23, MULHU=24, DIV_=25, DIVU=26, REM_=27, REMU=28;

  function automatic [5:0] decode_op(input [31:0] w);
    begin
      decode_op=63;
      case (w[6:0])
        7'h33: begin
          if (w[31:25]==1) begin
            case (w[14:12])
              0: decode_op=MUL; 1: decode_op=MULH; 2: decode_op=MULHSU; 3: decode_op=MULHU;
              4: decode_op=DIV_; 5: decode_op=DIVU; 6: decode_op=REM_; 7: decode_op=REMU;
            endcase
          end else if (w[31:25]==0) begin
            case (w[14:12])
              0: decode_op=ADD; 1: decode_op=SLL; 2: decode_op=SLT; 3: decode_op=SLTU;
              4: decode_op=XOR_; 5: decode_op=SRL; 6: decode_op=OR_; 7: decode_op=AND_;
            endcase
          end else if (w[31:25]==32 && w[14:12]==0) decode_op=SUB;
          else if (w[31:25]==32 && w[14:12]==5) decode_op=SRA;
        end
        7'h13: begin
          case (w[14:12])
            0: decode_op=ADDI; 2: decode_op=SLTI; 3: decode_op=SLTIU;
            4: decode_op=XORI; 6: decode_op=ORI; 7: decode_op=ANDI;
            1: if (w[31:25]==0) decode_op=SLLI;
            5: if (w[31:25]==0) decode_op=SRLI; else if (w[31:25]==32) decode_op=SRAI;
          endcase
        end
        7'h37: decode_op=LUI;
        7'h17: decode_op=AUIPC;
      endcase
    end
  endfunction

  function automatic [31:0] immediate(input [31:0] w);
    immediate = (w[6:0]==7'h37 || w[6:0]==7'h17) ?
      {w[31:12],12'b0} : {{20{w[31]}},w[31:20]};
  endfunction

  function automatic [31:0] alu(input [5:0] op,
    input [31:0] a,b,im,pc);
    reg signed [63:0] sa,sb,ub,product;
    reg [63:0] ua,prod_u;
    begin
      sa={{32{a[31]}},a}; sb={{32{b[31]}},b}; ub={32'b0,b}; ua={32'b0,a};
      product=0; prod_u=0;
      case (op)
        ADD: alu=a+b; SUB: alu=a-b; SLL: alu=a<<b[4:0];
        SLT: alu=($signed(a)<$signed(b)); SLTU: alu=(a<b);
        XOR_: alu=a^b; SRL: alu=a>>b[4:0]; SRA: alu=$signed(a)>>>b[4:0];
        OR_: alu=a|b; AND_: alu=a&b;
        ADDI: alu=a+im; SLTI: alu=($signed(a)<$signed(im)); SLTIU: alu=(a<im);
        XORI: alu=a^im; ORI: alu=a|im; ANDI: alu=a&im;
        SLLI: alu=a<<im[4:0]; SRLI: alu=a>>im[4:0]; SRAI: alu=$signed(a)>>>im[4:0];
        LUI: alu=im; AUIPC: alu=pc+im;
        MUL: alu=a*b;
        MULH: begin product=sa*sb; alu=product[63:32]; end
        MULHSU: begin product=sa*ub; alu=product[63:32]; end
        MULHU: begin prod_u=ua*{32'b0,b}; alu=prod_u[63:32]; end
        DIV_: begin
          if (b==0) alu=32'hffffffff;
          else if (a==32'h80000000 && b==32'hffffffff) alu=a;
          else alu=$signed(a)/$signed(b);
        end
        DIVU: alu=(b==0) ? 32'hffffffff : a/b;
        REM_: begin
          if (b==0) alu=a;
          else if (a==32'h80000000 && b==32'hffffffff) alu=0;
          else alu=$signed(a)%$signed(b);
        end
        REMU: alu=(b==0) ? a : a%b;
        default: alu=0;
      endcase
    end
  endfunction

  function automatic [5:0] wait_count(input [5:0] op);
    if (op>=25 && op<=28) wait_count=33;
    else if (op>=21 && op<=24) wait_count=2;
    else wait_count=0;
  endfunction

  reg [1023:0] regs, n_regs;
  reg [31:0] pc,n_pc;
  reg fv,dv,xv,mv,wv,n_fv,n_dv,n_xv,n_mv,n_wv;
  reg [31:0] fi,di,xi,mi,wi,n_fi,n_di,n_xi,n_mi,n_wi;
  reg [31:0] xval,mval,wval,n_xval,n_mval,n_wval;
  reg [31:0] xpc,mpc,wpc,n_xpc,n_mpc,n_wpc;
  reg [5:0] remaining,n_remaining;
  reg [31:0] a,b,projected_pc;
  reg [4:0] r1,r2;
  reg [5:0] op;

  assign retire_valid=!rst && wv && !stall_writeback;
  assign retire_insn=retire_valid ? wi : 0;
  assign retire_pc=retire_valid ? wpc : 0;
  assign retire_rd=retire_valid ? wi[11:7] : 0;
  assign retire_value=retire_valid ? wval : 0;
  assign debug_data=(debug_addr==0) ? 0 : regs[32*debug_addr +: 32];
  assign arch_pc=pc;
  assign occupancy={wv,mv,xv,dv,fv};

  always @* begin
    n_regs=regs; n_pc=pc;
    n_fv=fv; n_dv=dv; n_xv=xv; n_mv=mv; n_wv=wv;
    n_fi=fi; n_di=di; n_xi=xi; n_mi=mi; n_wi=wi;
    n_xval=xval; n_mval=mval; n_wval=wval;
    n_xpc=xpc; n_mpc=mpc; n_wpc=wpc;
    n_remaining=remaining;
    a=0; b=0; projected_pc=0; r1=0; r2=0; op=63;
    insn_ready=0;
    // Retire oldest first, then compute capacity freed on this edge.
    if (retire_valid) begin
      if (wi[11:7]!=0) n_regs[32*wi[11:7] +:32]=wval;
      n_pc=pc+4; n_wv=0;
    end
    if (!stall_memory && !n_wv) begin
      n_wv=n_mv; n_wi=n_mi; n_wval=n_mval; n_wpc=n_mpc; n_mv=0;
    end
    if (!stall_execute) begin
      if (n_remaining!=0) n_remaining=n_remaining-1;
      else if (!n_mv) begin
        n_mv=n_xv; n_mi=n_xi; n_mval=n_xval; n_mpc=n_xpc; n_xv=0;
      end
    end
    if (!stall_decode && !n_xv && n_dv) begin
      r1=n_di[19:15]; r2=n_di[24:20]; op=decode_op(n_di);
      a=(r1==0) ? 0 : n_regs[32*r1 +:32];
      b=(r2==0) ? 0 : n_regs[32*r2 +:32];
      // WB is older, MEM is younger: apply in this order.
      if (n_wv && n_wi[11:7]!=0 && n_wi[11:7]==r1) a=n_wval;
      if (n_wv && n_wi[11:7]!=0 && n_wi[11:7]==r2) b=n_wval;
      if (n_mv && n_mi[11:7]!=0 && n_mi[11:7]==r1) a=n_mval;
      if (n_mv && n_mi[11:7]!=0 && n_mi[11:7]==r2) b=n_mval;
      projected_pc=n_pc+(n_wv ? 4 : 0)+(n_mv ? 4 : 0);
      n_xval=alu(op,a,b,immediate(n_di),projected_pc);
      n_xi=n_di; n_xpc=projected_pc; n_xv=1; n_dv=0;
      n_remaining=wait_count(op);
    end
    if (!n_dv) begin n_dv=n_fv; n_di=n_fi; n_fv=0; end
    insn_ready=!rst && !stall_fetch && !n_fv && decode_op(insn)!=63;
    if (insn_valid && insn_ready) begin n_fv=1; n_fi=insn; end
  end

  always @(posedge clk) begin
    if (rst) begin
      regs<={reg_init[1023:32],32'b0}; pc<=0;
      fv<=0; dv<=0; xv<=0; mv<=0; wv<=0;
      fi<=0; di<=0; xi<=0; mi<=0; wi<=0;
      xval<=0; mval<=0; wval<=0; xpc<=0; mpc<=0; wpc<=0; remaining<=0;
    end else begin
      regs<=n_regs; pc<=n_pc;
      fv<=n_fv; dv<=n_dv; xv<=n_xv; mv<=n_mv; wv<=n_wv;
      fi<=n_fi; di<=n_di; xi<=n_xi; mi<=n_mi; wi<=n_wi;
      xval<=n_xval; mval<=n_mval; wval<=n_wval;
      xpc<=n_xpc; mpc<=n_mpc; wpc<=n_wpc; remaining<=n_remaining;
    end
  end
endmodule
