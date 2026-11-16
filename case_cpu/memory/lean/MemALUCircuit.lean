import MemPhysical
open LeanRTL MemCPUShallow
open CaseCPU
open CaseCPU.Bridge (high_ss high_su high_uu signed_div_eq signed_rem_eq)
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
theorem zsext (b : Word) : ((0#1) ++ b).signExtend 64 = b.setWidth 64 := by
  simp only [Word]
  bv_decide

theorem msb32 (a : Word) : a.msb = a[31] := by
  simp [BitVec.msb_eq_getLsbD_last]

theorem alu_add (b : Env) (hop : V_w467 b = opCode (.alu .add)) :
    V_w694 b = CaseCPU.calculate .add (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_add
theorem alu_sub (b : Env) (hop : V_w467 b = opCode (.alu .sub)) :
    V_w694 b = CaseCPU.calculate .sub (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_sub
theorem alu_sll (b : Env) (hop : V_w467 b = opCode (.alu .sll)) :
    V_w694 b = CaseCPU.calculate .sll (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_sll
theorem alu_slt (b : Env) (hop : V_w467 b = opCode (.alu .slt)) :
    V_w694 b = CaseCPU.calculate .slt (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_slt
theorem alu_sltu (b : Env) (hop : V_w467 b = opCode (.alu .sltu)) :
    V_w694 b = CaseCPU.calculate .sltu (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_sltu
theorem alu_xor (b : Env) (hop : V_w467 b = opCode (.alu .xor)) :
    V_w694 b = CaseCPU.calculate .xor (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_xor
theorem alu_srl (b : Env) (hop : V_w467 b = opCode (.alu .srl)) :
    V_w694 b = CaseCPU.calculate .srl (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_srl
theorem alu_sra (b : Env) (hop : V_w467 b = opCode (.alu .sra)) :
    V_w694 b = CaseCPU.calculate .sra (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_sra
theorem alu_or (b : Env) (hop : V_w467 b = opCode (.alu .or)) :
    V_w694 b = CaseCPU.calculate .or (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_or
theorem alu_and (b : Env) (hop : V_w467 b = opCode (.alu .and)) :
    V_w694 b = CaseCPU.calculate .and (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_and
theorem alu_addi (b : Env) (hop : V_w467 b = opCode (.alu .addi)) :
    V_w694 b = CaseCPU.calculate .addi (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_addi
theorem alu_slti (b : Env) (hop : V_w467 b = opCode (.alu .slti)) :
    V_w694 b = CaseCPU.calculate .slti (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_slti
theorem alu_sltiu (b : Env) (hop : V_w467 b = opCode (.alu .sltiu)) :
    V_w694 b = CaseCPU.calculate .sltiu (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_sltiu
theorem alu_xori (b : Env) (hop : V_w467 b = opCode (.alu .xori)) :
    V_w694 b = CaseCPU.calculate .xori (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_xori
theorem alu_ori (b : Env) (hop : V_w467 b = opCode (.alu .ori)) :
    V_w694 b = CaseCPU.calculate .ori (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_ori
theorem alu_andi (b : Env) (hop : V_w467 b = opCode (.alu .andi)) :
    V_w694 b = CaseCPU.calculate .andi (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_andi
theorem alu_slli (b : Env) (hop : V_w467 b = opCode (.alu .slli)) :
    V_w694 b = CaseCPU.calculate .slli (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_slli
theorem alu_srli (b : Env) (hop : V_w467 b = opCode (.alu .srli)) :
    V_w694 b = CaseCPU.calculate .srli (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_srli
theorem alu_srai (b : Env) (hop : V_w467 b = opCode (.alu .srai)) :
    V_w694 b = CaseCPU.calculate .srai (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_srai
theorem alu_lui (b : Env) (hop : V_w467 b = opCode (.alu .lui)) :
    V_w694 b = CaseCPU.calculate .lui (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_lui
theorem alu_auipc (b : Env) (hop : V_w467 b = opCode (.alu .auipc)) :
    V_w694 b = CaseCPU.calculate .auipc (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_auipc
theorem alu_mul (b : Env) (hop : V_w467 b = opCode (.alu .mul)) :
    V_w694 b = CaseCPU.calculate .mul (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_mul
theorem alu_mulh (b : Env) (hop : V_w467 b = opCode (.alu .mulh)) :
    V_w694 b = CaseCPU.calculate .mulh (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_mulh
theorem alu_mulhsu (b : Env) (hop : V_w467 b = opCode (.alu .mulhsu)) :
    V_w694 b = CaseCPU.calculate .mulhsu (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_mulhsu
theorem alu_mulhu (b : Env) (hop : V_w467 b = opCode (.alu .mulhu)) :
    V_w694 b = CaseCPU.calculate .mulhu (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_mulhu
theorem alu_div (b : Env) (hop : V_w467 b = opCode (.alu .div)) :
    V_w694 b = CaseCPU.calculate .div (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  by_cases hz : V_w574 b = 0
  · simp [hz, signedDiv, signedRem]
  by_cases ha : V_w577 b = 0x80000000
  · by_cases hb : V_w574 b = 0xffffffff
    · simp [ha, hb, signed_overflow, rem_overflow, signedDiv, signedRem]
    · cases hx : (V_w577 b)[31] <;> cases hy : (V_w574 b)[31] <;>
        simp_all [signed_div_eq, signed_rem_eq, BitVec.sdiv, BitVec.srem,
          msb32]
  · by_cases hb : V_w574 b = 0xffffffff <;>
      cases hx : (V_w577 b)[31] <;> cases hy : (V_w574 b)[31] <;>
        simp_all [signed_div_eq, signed_rem_eq, BitVec.sdiv, BitVec.srem,
          msb32]
#print axioms alu_div
theorem alu_divu (b : Env) (hop : V_w467 b = opCode (.alu .divu)) :
    V_w694 b = CaseCPU.calculate .divu (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_divu
theorem alu_rem (b : Env) (hop : V_w467 b = opCode (.alu .rem)) :
    V_w694 b = CaseCPU.calculate .rem (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  by_cases hz : V_w574 b = 0
  · simp [hz, signedDiv, signedRem]
  by_cases ha : V_w577 b = 0x80000000
  · by_cases hb : V_w574 b = 0xffffffff
    · simp [ha, hb, signed_overflow, rem_overflow, signedDiv, signedRem]
    · cases hx : (V_w577 b)[31] <;> cases hy : (V_w574 b)[31] <;>
        simp_all [signed_div_eq, signed_rem_eq, BitVec.sdiv, BitVec.srem,
          msb32]
  · by_cases hb : V_w574 b = 0xffffffff <;>
      cases hx : (V_w577 b)[31] <;> cases hy : (V_w574 b)[31] <;>
        simp_all [signed_div_eq, signed_rem_eq, BitVec.sdiv, BitVec.srem,
          msb32]
#print axioms alu_rem
theorem alu_remu (b : Env) (hop : V_w467 b = opCode (.alu .remu)) :
    V_w694 b = CaseCPU.calculate .remu (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
  simp only [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w614,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hop,opCode,CaseCPU.Bridge.opCode]
  simp [CaseCPU.calculate,CaseCPU.bit,BitVec.toNat_setWidth,high_ss,high_su,high_uu,zsext]
  all_goals try {split <;> rfl}
#print axioms alu_remu
theorem circuit_alu (b : Env) (op : CaseCPU.Op) (h : V_w467 b = opCode (.alu op)) :
    V_w694 b = CaseCPU.calculate op (V_w577 b) (V_w574 b) (V_w580 b) (V_w659 b) := by
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
end CaseCPUMem.Source
