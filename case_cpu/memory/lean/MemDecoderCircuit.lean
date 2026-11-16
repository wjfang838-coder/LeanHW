import MemDecode
import MemoryCircuit
import Std.Tactic.BVDecide
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
theorem decoder_w384 (b : Env) : V_w384 b = codeBits (b.lookup "insn" 32) := by
  simp only [V_w384,V_w167,V_w152,V_w126,V_w125,V_w128,V_w127,V_w326,V_w324,V_w298,V_w253,V_w252,V_w121,V_w15,V_w16,V_w299,V_w234,V_w159,V_w120,V_w119,V_w232,V_w233,V_w325,V_w231,V_w170,V_w117,V_w116,V_w228,V_w227,V_w230,V_w229,V_w383,V_w153,V_w130,V_w129,V_w381,V_w372,V_w332,V_w169,V_w157,V_w115,V_w114,V_w331,V_w330,V_w226,V_w122,V_w225,V_w124,V_w301,V_w300,V_w207,V_w224,V_w158,V_w118,V_w222,V_w223,V_w382,V_w131,V_w329,V_w154,V_w123,V_w327,V_w221,V_w220,V_w302,V_w219,V_w168,V_w155,V_w215,V_w214,V_w208,V_w218,V_w156,V_w216,V_w217,V_w328,V_w213,V_w209,V_w212,V_w210,V_w211,codeBits,loadCode,storeCode,CaseCPU.Bridge.codeBits,CaseCPU.Bridge.codeFields,Word,CaseCPU.Word]
  bv_decide
#print axioms decoder_w384
theorem decoder_w380 (b : Env) : V_w380 b = codeBits (b.lookup "r21" 32) := by
  simp only [V_w380,V_w163,V_w144,V_w51,V_w50,V_w52,V_w53,V_w315,V_w313,V_w266,V_w251,V_w250,V_w46,V_w13,V_w14,V_w267,V_w206,V_w151,V_w45,V_w44,V_w204,V_w205,V_w314,V_w203,V_w166,V_w42,V_w41,V_w200,V_w199,V_w202,V_w201,V_w379,V_w145,V_w55,V_w54,V_w377,V_w338,V_w321,V_w165,V_w149,V_w40,V_w39,V_w320,V_w319,V_w198,V_w47,V_w197,V_w49,V_w269,V_w268,V_w179,V_w196,V_w150,V_w43,V_w194,V_w195,V_w378,V_w56,V_w318,V_w146,V_w48,V_w316,V_w193,V_w192,V_w270,V_w191,V_w164,V_w147,V_w187,V_w186,V_w180,V_w190,V_w148,V_w188,V_w189,V_w317,V_w185,V_w181,V_w184,V_w182,V_w183,codeBits,loadCode,storeCode,CaseCPU.Bridge.codeBits,CaseCPU.Bridge.codeFields,Word,CaseCPU.Word]
  bv_decide
#print axioms decoder_w380
end CaseCPUMem.Source
