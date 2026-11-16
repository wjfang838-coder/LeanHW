import Circuit
import WordMath
import DecoderTable
open LeanRTL CPUShallow
namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable def immediateBits (b : Env) : Word := ((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b
theorem immediate_low (b : Env) : (V_w105 b).setWidth 5 = (immediateBits b).setWidth 5 := by
  unfold immediateBits
  try simp only [Word]
  bv_decide

theorem zsext (b : Word) : ((0#1) ++ b).signExtend 64 = b.setWidth 64 := by
  try simp only [Word]
  bv_decide

theorem msb32 (a : Word) : a.msb = a[31] := by
  simp [BitVec.msb_eq_getLsbD_last]

theorem alu_add (b : Env) (hop : V_w197 b = opCode .add) :
    V_w331 b = calculate .add (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_add
theorem alu_sub (b : Env) (hop : V_w197 b = opCode .sub) :
    V_w331 b = calculate .sub (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_sub
theorem alu_sll (b : Env) (hop : V_w197 b = opCode .sll) :
    V_w331 b = calculate .sll (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_sll
theorem alu_slt (b : Env) (hop : V_w197 b = opCode .slt) :
    V_w331 b = calculate .slt (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
  split <;> rfl
#print axioms alu_slt
theorem alu_sltu (b : Env) (hop : V_w197 b = opCode .sltu) :
    V_w331 b = calculate .sltu (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
  split <;> rfl
#print axioms alu_sltu
theorem alu_xor (b : Env) (hop : V_w197 b = opCode .xor) :
    V_w331 b = calculate .xor (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_xor
theorem alu_srl (b : Env) (hop : V_w197 b = opCode .srl) :
    V_w331 b = calculate .srl (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_srl
theorem alu_sra (b : Env) (hop : V_w197 b = opCode .sra) :
    V_w331 b = calculate .sra (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_sra
theorem alu_or (b : Env) (hop : V_w197 b = opCode .or) :
    V_w331 b = calculate .or (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_or
theorem alu_and (b : Env) (hop : V_w197 b = opCode .and) :
    V_w331 b = calculate .and (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_and
theorem alu_addi (b : Env) (hop : V_w197 b = opCode .addi) :
    V_w331 b = calculate .addi (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_addi
theorem alu_slti (b : Env) (hop : V_w197 b = opCode .slti) :
    V_w331 b = calculate .slti (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
  split <;> rfl
#print axioms alu_slti
theorem alu_sltiu (b : Env) (hop : V_w197 b = opCode .sltiu) :
    V_w331 b = calculate .sltiu (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
  split <;> rfl
#print axioms alu_sltiu
theorem alu_xori (b : Env) (hop : V_w197 b = opCode .xori) :
    V_w331 b = calculate .xori (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_xori
theorem alu_ori (b : Env) (hop : V_w197 b = opCode .ori) :
    V_w331 b = calculate .ori (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_ori
theorem alu_andi (b : Env) (hop : V_w197 b = opCode .andi) :
    V_w331 b = calculate .andi (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_andi
theorem alu_slli (b : Env) (hop : V_w197 b = opCode .slli) :
    V_w331 b = calculate .slli (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_slli
theorem alu_srli (b : Env) (hop : V_w197 b = opCode .srli) :
    V_w331 b = calculate .srli (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_srli
theorem alu_srai (b : Env) (hop : V_w197 b = opCode .srai) :
    V_w331 b = calculate .srai (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_srai
theorem alu_lui (b : Env) (hop : V_w197 b = opCode .lui) :
    V_w331 b = calculate .lui (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_lui
theorem alu_auipc (b : Env) (hop : V_w197 b = opCode .auipc) :
    V_w331 b = calculate .auipc (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_auipc
theorem alu_mul (b : Env) (hop : V_w197 b = opCode .mul) :
    V_w331 b = calculate .mul (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_mul
theorem alu_mulh (b : Env) (hop : V_w197 b = opCode .mulh) :
    V_w331 b = calculate .mulh (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_mulh
theorem alu_mulhsu (b : Env) (hop : V_w197 b = opCode .mulhsu) :
    V_w331 b = calculate .mulhsu (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_mulhsu
theorem alu_mulhu (b : Env) (hop : V_w197 b = opCode .mulhu) :
    V_w331 b = calculate .mulhu (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
#print axioms alu_mulhu
theorem alu_div (b : Env) (hop : V_w197 b = opCode .div) :
    V_w331 b = calculate .div (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
  by_cases hz : V_w195 b = 0
  · simp [hz, signedDiv, signedRem]
  by_cases ha : V_w249 b = 0x80000000
  · by_cases hb : V_w195 b = 0xffffffff
    · simp [ha, hb, signed_overflow, rem_overflow, signedDiv, signedRem]
    · cases hx : (V_w249 b)[31] <;> cases hy : (V_w195 b)[31] <;>
        simp_all [signed_div_eq, signed_rem_eq, BitVec.sdiv, BitVec.srem,
          msb32]
  · by_cases hb : V_w195 b = 0xffffffff <;>
      cases hx : (V_w249 b)[31] <;> cases hy : (V_w195 b)[31] <;>
        simp_all [signed_div_eq, signed_rem_eq, BitVec.sdiv, BitVec.srem,
          msb32]
#print axioms alu_div
theorem alu_divu (b : Env) (hop : V_w197 b = opCode .divu) :
    V_w331 b = calculate .divu (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
  split <;> simp_all
#print axioms alu_divu
theorem alu_rem (b : Env) (hop : V_w197 b = opCode .rem) :
    V_w331 b = calculate .rem (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
  by_cases hz : V_w195 b = 0
  · simp [hz, signedDiv, signedRem]
  by_cases ha : V_w249 b = 0x80000000
  · by_cases hb : V_w195 b = 0xffffffff
    · simp [ha, hb, signed_overflow, rem_overflow, signedDiv, signedRem]
    · cases hx : (V_w249 b)[31] <;> cases hy : (V_w195 b)[31] <;>
        simp_all [signed_div_eq, signed_rem_eq, BitVec.sdiv, BitVec.srem,
          msb32]
  · by_cases hb : V_w195 b = 0xffffffff <;>
      cases hx : (V_w249 b)[31] <;> cases hy : (V_w195 b)[31] <;>
        simp_all [signed_div_eq, signed_rem_eq, BitVec.sdiv, BitVec.srem,
          msb32]
#print axioms alu_rem
theorem alu_remu (b : Env) (hop : V_w197 b = opCode .remu) :
    V_w331 b = calculate .remu (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  simp only [V_w331, V_w330, V_w329, V_w328, V_w327, V_w326, V_w325, V_w324, V_w323, V_w322, V_w321, V_w320, V_w319, V_w318, V_w317, V_w316, V_w315, V_w314, V_w313, V_w312, V_w311, V_w310, V_w309, V_w308, V_w307, V_w306, V_w305, V_w304, V_w300, V_w299, V_w298, V_w297, V_w296, V_w295, V_w294, V_w293, V_w292, V_w291, V_w290, V_w289, V_w287, V_w286, V_w285, V_w284, V_w283, V_w282, V_w281, V_w280, V_w279, V_w278, V_w277, V_w276, V_w275, V_w274, V_w273, V_w272, V_w271, V_w270, V_w269, V_w268, V_w267, V_w266, V_w265, V_w264, V_w263, V_w262, V_w261, V_w260, V_w259, V_w258, V_w257, V_w256, V_w255, V_w254, V_w253, V_w252, V_w251, V_w247, V_w246, V_w245, V_w244, V_w243, V_w242, V_w241, V_w240, V_w239, V_w238, V_w237, V_w236, V_w235, V_w234, V_w233, V_w232, V_w231, V_w230, V_w229, V_w228, V_w227, V_w226, V_w225, V_w224, V_w223, V_w222, V_w221, V_w220, V_w219, V_w203, V_w202, V_w177, hop, opCode]
  try change _ = calculate _ _ _ (((b.lookup "r11" 32 >>> 31).setWidth 1) ++ V_w105 b) _
  simp [calculate, bit, BitVec.toNat_setWidth, immediateBits, immediate_low, zsext, high_ss, high_su, high_uu]
  split <;> simp_all
#print axioms alu_remu
theorem circuit_alu (b : Env) (op : Op) (h : V_w197 b = opCode op) :
    V_w331 b = calculate op (V_w249 b) (V_w195 b) (immediateBits b) (V_w176 b) := by
  cases op
  · exact alu_add b h
  · exact alu_sub b h
  · exact alu_sll b h
  · exact alu_slt b h
  · exact alu_sltu b h
  · exact alu_xor b h
  · exact alu_srl b h
  · exact alu_sra b h
  · exact alu_or b h
  · exact alu_and b h
  · exact alu_addi b h
  · exact alu_slti b h
  · exact alu_sltiu b h
  · exact alu_xori b h
  · exact alu_ori b h
  · exact alu_andi b h
  · exact alu_slli b h
  · exact alu_srli b h
  · exact alu_srai b h
  · exact alu_lui b h
  · exact alu_auipc b h
  · exact alu_mul b h
  · exact alu_mulh b h
  · exact alu_mulhsu b h
  · exact alu_mulhu b h
  · exact alu_div b h
  · exact alu_divu b h
  · exact alu_rem b h
  · exact alu_remu b h
#print axioms circuit_alu
end CaseCPU.Bridge
