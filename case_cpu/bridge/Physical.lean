import ImportedData
import RawCPU

namespace CaseCPU.Bridge
open LeanRTL
set_option linter.unusedSimpArgs false

/-- The names below are bound by the RTLIL register map, not guessed from behavior. -/
def rawOf (r : Env) : Raw := {
  rf := r.lookup "r3" 1024
  pc := r.lookup "r4" 32
  fi := r.lookup "r10" 32
  di := r.lookup "r11" 32
  x := ⟨r.lookup "r12" 32,r.lookup "r15" 32,r.lookup "r18" 32⟩
  m := ⟨r.lookup "r13" 32,r.lookup "r16" 32,r.lookup "r0" 32⟩
  w := ⟨r.lookup "r14" 32,r.lookup "r17" 32,r.lookup "r1" 32⟩
  fv := r.lookup "r5" 1 == 1
  dv := r.lookup "r6" 1 == 1
  xv := r.lookup "r7" 1 == 1
  mv := r.lookup "r8" 1 == 1
  wv := r.lookup "r9" 1 == 1
  remaining := r.lookup "r2" 6 }

def pinEnv (i : Pins) (o : Env) : Env := fun n =>
  if n = "clk" then 1 else
  if n = "rst" then i.reset.toNat else
  if n = "reg_init" then i.seed.toNat else
  if n = "insn" then i.word.toNat else
  if n = "insn_valid" then i.valid.toNat else
  if n = "stall_fetch" then i.sf.toNat else
  if n = "stall_decode" then i.sd.toNat else
  if n = "stall_execute" then i.sx.toNat else
  if n = "stall_memory" then i.sm.toNat else
  if n = "stall_writeback" then i.sw.toNat else
  if n = "debug_addr" then i.debug.toNat else o n

def base (r : Env) (i : Pins) (o : Env) : Env :=
  cycleEnv r (pinEnv i o) (V2LeanImported.core.regs.map (·.name))

def rtlStep (r : Env) (i : Pins) (o : Env) : Env :=
  V2LeanImported.core.step r (pinEnv i o) false

def rtlRun : Env → List (Pins × Env) → Env
  | r, [] => r
  | r, (i,o)::xs => rtlRun (rtlStep r i o) xs

def rawRun : Raw → List Pins → Raw
  | s, [] => s
  | s, i::xs => rawRun (rawCycle s i) xs

theorem projected_run (s : Raw) (xs : List Pins) :
    project (rawRun s xs) = run (project s) (xs.map specInput) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [rawRun,List.map_cons,run,ih,project_cycle]

def Legal (s : Raw) : Prop :=
  (s.fv = true → (CaseCPU.decode s.fi).isSome = true) ∧
  (s.dv = true → (CaseCPU.decode s.di).isSome = true) ∧
  (s.xv = true → (CaseCPU.decode s.x.word).isSome = true) ∧
  (s.mv = true → (CaseCPU.decode s.m.word).isSome = true) ∧
  (s.wv = true → (CaseCPU.decode s.w.word).isSome = true)

theorem legal_initial (seed : RF) : Legal (rawInitial seed) := by
  simp [Legal,rawInitial]

theorem legal_commit (s : Raw) (b : Bool) (h : Legal s) : Legal (commitRaw s b) := by
  unfold commitRaw
  split <;> simp_all [Legal]

theorem legal_memory (s : Raw) (b : Bool) (h : Legal s) : Legal (memoryRaw s b) := by
  unfold memoryRaw
  split <;> simp_all [Legal]

theorem legal_execute (s : Raw) (b : Bool) (h : Legal s) : Legal (executeRaw s b) := by
  unfold executeRaw
  split <;> try exact h
  split <;> try simpa [Legal] using h
  split <;> simp_all [Legal]

theorem legal_dispatch (s : Raw) (b : Bool) (h : Legal s) : Legal (dispatchRaw s b) := by
  unfold dispatchRaw
  split <;> simp_all [Legal]

theorem legal_fetch (s : Raw) (h : Legal s) : Legal (fetchRaw s) := by
  unfold fetchRaw
  split <;> simp_all [Legal]

theorem legal_accept (s : Raw) (i : Pins) (h : Legal s) : Legal (acceptRaw s i).1 := by
  unfold acceptRaw readyRaw
  split <;> simp_all [Legal]

theorem legal_cycle (s : Raw) (i : Pins) (h : Legal s) : Legal (rawCycle s i) := by
  unfold rawCycle
  split
  · exact legal_initial _
  · exact legal_accept _ _ (legal_fetch _ (legal_dispatch _ _
      (legal_execute _ _ (legal_memory _ _ (legal_commit _ _ h)))))

#print axioms projected_run
#print axioms legal_cycle
end CaseCPU.Bridge
