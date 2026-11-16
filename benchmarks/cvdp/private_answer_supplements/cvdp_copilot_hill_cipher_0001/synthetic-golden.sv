module hill_cipher(input wire clk,reset,start,input wire[14:0] plaintext,input wire[44:0] key,output reg[14:0] ciphertext,output reg done);
reg[1:0] phase;reg[14:0] p;reg[44:0] k;reg busy;integer i,j,acc;reg[14:0] result;
always @* begin
 result=0;
 for(i=0;i<3;i=i+1)begin
  acc=0;
  for(j=0;j<3;j=j+1)acc=acc+((k>>(5*(8-(3*i+j))))&31)*((p>>(5*(2-j)))&31);
  result=result | ((acc%26)<<(5*(2-i)));
 end
end
always @(posedge clk or posedge reset)begin
 if(reset)begin ciphertext<=0;done<=0;busy<=0;phase<=0;p<=0;k<=0;end
 else begin
  done<=0;
  if(busy)begin
   if(phase==2)begin ciphertext<=result;done<=1;busy<=0;phase<=0;end
   else phase<=phase+1;
  end else if(start)begin p<=plaintext;k<=key;busy<=1;phase<=0;end
 end
end
endmodule
