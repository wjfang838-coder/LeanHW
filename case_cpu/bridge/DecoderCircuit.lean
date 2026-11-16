import Circuit
import DecoderTable
import Std.Tactic.BVDecide
open LeanRTL CPUShallow
namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
theorem circuit_w140 (b : Env) : V_w140 b = codeBits (b.lookup "insn" 32) := by
  simp only [V_w140, V_w139, V_w138, V_w120, V_w119, V_w117, V_w116, V_w112, V_w111, V_w110, V_w99, V_w98, V_w97, V_w95, V_w94, V_w93, V_w92, V_w85, V_w83, V_w80, V_w79, V_w78, V_w77, V_w76, V_w70, V_w68, V_w67, V_w66, V_w42, V_w41, V_w40, V_w39, V_w38, V_w37, V_w36, V_w35, V_w34, V_w33, V_w32, V_w31, V_w30, V_w29, V_w28, V_w24, V_w23, V_w22, V_w21, V_w20, V_w9, V_w8, V_w4, codeBits, codeFields]
  simp only [Word]
  bv_decide
#print axioms circuit_w140
theorem circuit_w137 (b : Env) : V_w137 b = codeBits (b.lookup "r11" 32) := by
  simp only [V_w137, V_w136, V_w135, V_w122, V_w121, V_w115, V_w114, V_w109, V_w108, V_w107, V_w102, V_w101, V_w100, V_w91, V_w90, V_w89, V_w88, V_w86, V_w84, V_w75, V_w74, V_w73, V_w72, V_w71, V_w69, V_w65, V_w64, V_w63, V_w57, V_w56, V_w55, V_w54, V_w53, V_w52, V_w51, V_w50, V_w49, V_w48, V_w47, V_w46, V_w45, V_w44, V_w43, V_w19, V_w18, V_w17, V_w16, V_w15, V_w7, V_w6, V_w5, codeBits, codeFields]
  simp only [Word]
  bv_decide
#print axioms circuit_w137
end CaseCPU.Bridge
