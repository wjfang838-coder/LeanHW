// Independent instruction-oriented reference, used only by the verification miter.
// The DUT's decode_op/alu are deliberately not called here.
function automatic [31:0] reference_value(input [31:0] w,a,b,at_pc);
  reg [31:0] imm;
  reg signed [63:0] prod;
  reg [63:0] uprod;
  begin
    imm={{20{w[31]}},w[31:20]}; prod=0; uprod=0; reference_value=0;
    case(w[6:0])
      7'h37: reference_value={w[31:12],12'b0};
      7'h17: reference_value=at_pc+{w[31:12],12'b0};
      7'h13: case(w[14:12])
        0: reference_value=a+imm;
        1: reference_value=a<<w[24:20];
        2: reference_value=($signed(a)<$signed(imm));
        3: reference_value=(a<imm);
        4: reference_value=a^imm;
        5: if(w[30]) reference_value=$signed(a)>>>w[24:20];
           else reference_value=a>>w[24:20];
        6: reference_value=a|imm; 7: reference_value=a&imm;
      endcase
      7'h33: if(w[25]) begin
        case(w[14:12])
          0: reference_value=a*b;
          1: begin prod=$signed({{32{a[31]}},a})*$signed({{32{b[31]}},b}); reference_value=prod[63:32]; end
          2: begin prod=$signed({{32{a[31]}},a})*$signed({32'b0,b}); reference_value=prod[63:32]; end
          3: begin uprod={32'b0,a}*{32'b0,b}; reference_value=uprod[63:32]; end
          4: begin
            if(b==0) reference_value=32'hffffffff;
            else if(a==32'h80000000 && b==32'hffffffff) reference_value=32'h80000000;
            else reference_value=$signed(a)/$signed(b);
          end
          5: if(b==0) reference_value=32'hffffffff; else reference_value=a/b;
          6: begin
            if(b==0) reference_value=a;
            else if(a==32'h80000000 && b==32'hffffffff) reference_value=0;
            else reference_value=$signed(a)%$signed(b);
          end
          7: if(b==0) reference_value=a; else reference_value=a%b;
        endcase
      end else case(w[14:12])
        0: if(w[30]) reference_value=a-b; else reference_value=a+b;
        1: reference_value=a<<b[4:0];
        2: reference_value=($signed(a)<$signed(b)); 3: reference_value=(a<b);
        4: reference_value=a^b;
        5: if(w[30]) reference_value=$signed(a)>>>b[4:0]; else reference_value=a>>b[4:0];
        6: reference_value=a|b; 7: reference_value=a&b;
      endcase
    endcase
  end
endfunction
