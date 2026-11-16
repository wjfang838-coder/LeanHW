import Refinement
namespace CaseCPU
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

inductive Fault where
  | fixed | noForward | divZero | ignoreWritebackStall
  deriving DecidableEq

def faultDispatch (f : Fault) (s : Pipe) (stall : Bool) : Pipe :=
  if stall then s else
  match s.execute, s.decodeStage with
  | none, some i =>
    let a := if f = .noForward then s.arch else forwarded s
    let e := effectFor a i
    let e := if f = .divZero ∧ i.op = .div ∧ readReg a i.rs2 = 0 then
      { e with value := 0 } else e
    { s with execute := some ⟨i,e⟩, remaining := latency i.op - 1, decodeStage := none }
  | _, _ => s

def faultCycle (f : Fault) (s : Pipe) (i : Input) : Outcome :=
  if i.reset then ⟨initial i.initRegs, none, false⟩ else
  let (s1, retired) := retire s (if f = .ignoreWritebackStall then false else i.stallWriteback)
  let s2 := moveMemory s1 i.stallMemory
  let s3 := moveExecute s2 i.stallExecute
  let s4 := faultDispatch f s3 i.stallDecode
  let (s5, accepted) := accept (moveFetch s4) i
  ⟨s5, retired, accepted⟩

def faultRun (f : Fault) : Pipe → List Input → Pipe
  | s, [] => s
  | s, i :: is => faultRun f (faultCycle f s i).state is

def dependencyTrace : List Input :=
  [{valid := true, word := 0x00700093}, -- ADDI x1,x0,7
   {valid := true, word := 0x00908113}] ++ List.replicate 7 ({ reset := false } : Input) -- ADDI x2,x1,9

def divisionTrace : List Input :=
  [{valid := true, word := 0x0200c1b3}] ++ List.replicate 40 ({ reset := false } : Input) -- DIV x3,x1,x0

def blockedTrace : List Input :=
  [{valid := true, word := 0x00700093}] ++ List.replicate 4 ({ reset := false } : Input) ++ [{stallWriteback := true}]

theorem no_forward_counterexample :
    readReg (run (initial (fun _ => 0)) dependencyTrace).arch 2 = 16 ∧
    readReg (faultRun .noForward (initial (fun _ => 0)) dependencyTrace).arch 2 = 9 := by
  decide +kernel

theorem divide_zero_counterexample :
    readReg (run (initial (fun _ => 7)) divisionTrace).arch 3 = 0xffffffff ∧
    readReg (faultRun .divZero (initial (fun _ => 7)) divisionTrace).arch 3 = 0 := by
  decide +kernel

theorem stalled_retirement_counterexample :
    (run (initial (fun _ => 0)) blockedTrace).arch.pc = 0 ∧
    (faultRun .ignoreWritebackStall (initial (fun _ => 0)) blockedTrace).arch.pc = 4 := by
  decide +kernel

theorem fixed_dispatch (s : Pipe) (b : Bool) : faultDispatch .fixed s b = dispatch s b := by
  cases b <;> cases he : s.execute <;> cases hd : s.decodeStage <;>
    simp [faultDispatch, dispatch, he, hd]

theorem fixed_cycle (s : Pipe) (i : Input) : faultCycle .fixed s i = cycle s i := by
  simp [faultCycle, cycle, fixed_dispatch]

theorem fixed_run (s : Pipe) (xs : List Input) : faultRun .fixed s xs = run s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp [faultRun, run, fixed_cycle, ih]

theorem corrected_refinement (rf : Reg → Word) (xs : List Input) :
    (faultRun .fixed (initial rf) xs).arch = reference (initial rf) (initial rf).arch xs := by
  rw [fixed_run]
  exact reset_refinement rf xs

#print axioms no_forward_counterexample
#print axioms divide_zero_counterexample
#print axioms stalled_retirement_counterexample
#print axioms corrected_refinement
end CaseCPU
