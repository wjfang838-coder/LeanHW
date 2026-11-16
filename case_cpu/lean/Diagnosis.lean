import LeanSpec

/-! Clause-local diagnostic projection of original.txt. Enumerated witnesses are not
    a bounded CPU model and their completeness is not completeness over CPU traces. -/
namespace CPUDiagnosis
open LeanSpec
set_option linter.unusedSimpArgs false

inductive Ctx where
  | wbDuringExStall | competingWriters | divideByZero | zeroDestination
  | resetWithWriteback | multiplyLatency | permanentlyBlocked
  deriving DecidableEq, Repr
inductive KStall where | local | global deriving DecidableEq, Repr
inductive KForward where | youngest | oldest deriving DecidableEq, Repr
inductive KLatency where | includesEntry | afterEntry deriving DecidableEq, Repr
inductive KReset where | bothClauses | resetPriority | retirePriority deriving DecidableEq, Repr

structure Cfg where
  c_stall : KStall := .local
  c_forward : KForward := .youngest
  c_latency : KLatency := .includesEntry
  c_reset : KReset := .bothClauses
  h_divzero : Option (BitVec 32) := none
  h_x0 : Option (BitVec 32) := none
  requireDeadline : Bool := true

def ctxUniverse : List Ctx := [.wbDuringExStall, .competingWriters, .divideByZero,
  .zeroDestination, .resetWithWriteback, .multiplyLatency, .permanentlyBlocked]
def obsUniverse : List (BitVec 32) := [0,1,3,4,7,9,0xffffffff]
def ctxCost : Ctx → Nat
  | .multiplyLatency => 3
  | .permanentlyBlocked => 41
  | _ => 1
def legal (_ : Ctx) : Bool := true

def admits (cfg : Cfg) (c : Ctx) (o : BitVec 32) : Bool :=
  match c with
  | .wbDuringExStall => o == (if cfg.c_stall == .local then 1 else 0)
  | .competingWriters => o == (if cfg.c_forward == .youngest then 9 else 7)
  | .multiplyLatency => o == (if cfg.c_latency == .includesEntry then 3 else 4)
  | .divideByZero => cfg.h_divzero.isNone || cfg.h_divzero == some o
  | .zeroDestination => cfg.h_x0.isNone || cfg.h_x0 == some o
  | .resetWithWriteback => match cfg.c_reset with
    | .bothClauses => o == 0 && o == 1
    | .resetPriority => o == 0
    | .retirePriority => o == 1
  | .permanentlyBlocked => o == 0 && (!cfg.requireDeadline || o == 1)

def defaultCfg : Cfg := {}
def consistentCfg : Cfg := { c_reset := .resetPriority, requireDeadline := false }
def revised : Cfg where
  c_reset := .resetPriority
  h_divzero := some 0xffffffff
  h_x0 := some 0
  requireDeadline := false
def globalStall : Cfg := { consistentCfg with c_stall := .global }
def oldestForward : Cfg := { consistentCfg with c_forward := .oldest }
def extraCycle : Cfg := { consistentCfg with c_latency := .afterEntry }

def ctxName : Ctx → String
  | .wbDuringExStall => "WB valid, EX externally stalled, WB unblocked"
  | .competingWriters => "older WB writes x1=7; younger MEM writes x1=9; ID reads x1"
  | .divideByZero => "DIV x3,x1,x0 with x1=7"
  | .zeroDestination => "ADDI x0,x0,7; observe x0"
  | .resetWithWriteback => "reset=1 and WB valid on the same edge"
  | .multiplyLatency => "MUL enters EX; three unblocked EX edges including entry"
  | .permanentlyBlocked => "accepted instruction, WB blocked for 41 edges"
def ctxLean : Ctx → String
  | .wbDuringExStall => "CPUDiagnosis.Ctx.wbDuringExStall"
  | .competingWriters => "CPUDiagnosis.Ctx.competingWriters"
  | .divideByZero => "CPUDiagnosis.Ctx.divideByZero"
  | .zeroDestination => "CPUDiagnosis.Ctx.zeroDestination"
  | .resetWithWriteback => "CPUDiagnosis.Ctx.resetWithWriteback"
  | .multiplyLatency => "CPUDiagnosis.Ctx.multiplyLatency"
  | .permanentlyBlocked => "CPUDiagnosis.Ctx.permanentlyBlocked"
def case : Case Ctx (BitVec 32) := {
  ctxs := ctxUniverse, obs := obsUniverse, legal := legal, cost := ctxCost,
  ctxJson := fun c => jobj [("scenario", jstr (ctxName c))],
  ctxLean := ctxLean, obsJson := fun o => jnat o.toNat }

-- These certificates state the same witness terms returned by the actual queries.
theorem stall_ambiguity : queryDifference (admits consistentCfg) (admits globalStall)
    obsUniverse ctxUniverse legal = some .wbDuringExStall := by decide +kernel
theorem forwarding_ambiguity : queryDifference (admits consistentCfg) (admits oldestForward)
    obsUniverse ctxUniverse legal = some .competingWriters := by decide +kernel
theorem latency_ambiguity : queryDifference (admits consistentCfg) (admits extraCycle)
    obsUniverse ctxUniverse legal = some .multiplyLatency := by decide +kernel
theorem divzero_incomplete : 1 < (admitSet (admits defaultCfg) obsUniverse .divideByZero).length := by decide +kernel
theorem x0_incomplete : 1 < (admitSet (admits defaultCfg) obsUniverse .zeroDestination).length := by decide +kernel
theorem reset_contradiction : admitSet (admits defaultCfg) obsUniverse .resetWithWriteback = [] := by decide +kernel
theorem progress_contradiction : admitSet (admits defaultCfg) obsUniverse .permanentlyBlocked = [] := by decide +kernel
theorem revised_projection_determined :
    determinedEverywhere (admits revised) obsUniverse ctxUniverse legal = true := by decide +kernel

#eval emitDomain case
#eval emitDeadness case "original" (admits defaultCfg)
#eval emitDeadness {case with ctxs := [.permanentlyBlocked]} "progress" (admits defaultCfg)
#eval emitDifference case "stall" "local" "global" (admits consistentCfg) (admits globalStall)
#eval emitDifference case "forward" "youngest" "oldest" (admits consistentCfg) (admits oldestForward)
#eval emitDifference case "latency" "includesEntry" "afterEntry" (admits consistentCfg) (admits extraCycle)
#eval emitHole case "divzero" (admits defaultCfg) (admits {defaultCfg with h_divzero := some 0xffffffff})
#eval emitHole case "x0" (admits defaultCfg) (admits {defaultCfg with h_x0 := some 0})
#eval emitDecided case "revised" (admits revised)
#print axioms stall_ambiguity
#print axioms forwarding_ambiguity
#print axioms latency_ambiguity
#print axioms divzero_incomplete
#print axioms x0_incomplete
#print axioms reset_contradiction
#print axioms progress_contradiction
#print axioms revised_projection_determined
end CPUDiagnosis
