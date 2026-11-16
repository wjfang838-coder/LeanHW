import Refinement

namespace CaseCPU
def encode (i : Instr) : Word :=
  let pair : Nat × Nat := match i.op with
    | .add => (0,0) | .sub => (32,0) | .sll => (0,1) | .slt => (0,2)
    | .sltu => (0,3) | .xor => (0,4) | .srl => (0,5) | .sra => (32,5)
    | .or => (0,6) | .and => (0,7)
    | .mul => (1,0) | .mulh => (1,1) | .mulhsu => (1,2) | .mulhu => (1,3)
    | .div => (1,4) | .divu => (1,5) | .rem => (1,6) | .remu => (1,7)
    | _ => (0,0)
  let n := match i.op with
    | .lui => i.imm.toNat / 4096 * 4096 + i.rd.toNat * 128 + 0x37
    | .auipc => i.imm.toNat / 4096 * 4096 + i.rd.toNat * 128 + 0x17
    | .addi | .slti | .sltiu | .xori | .ori | .andi | .slli | .srli | .srai =>
      let f3 := match i.op with
        | .addi => 0 | .slti => 2 | .sltiu => 3 | .xori => 4
        | .ori => 6 | .andi => 7 | .slli => 1 | _ => 5
      i.imm.toNat % 4096 * 2^20 + i.rs1.toNat * 2^15 + f3 * 4096 + i.rd.toNat * 128 + 0x13
    | _ => pair.1 * 2^25 + i.rs2.toNat * 2^20 + i.rs1.toNat * 2^15 +
      pair.2 * 4096 + i.rd.toNat * 128 + 0x33
  BitVec.ofNat 32 n

def occupancy (s : Pipe) : Nat :=
  (if s.fetch.isSome then 1 else 0) + (if s.decodeStage.isSome then 2 else 0) +
  (if s.execute.isSome then 4 else 0) + (if s.memory.isSome then 8 else 0) +
  (if s.writeback.isSome then 16 else 0)

def traceMain (argv : List String) : IO Unit := do
  let args := argv.toArray
  if args.size != 2 then throw (IO.userError "Trace.lean INPUT OUTPUT")
  let src ← IO.FS.readFile args[0]!
  let out ← IO.FS.Handle.mk args[1]! .write
  let mut s := initial (fun _ => 0)
  for line in src.splitOn "\n" do
    if line.isEmpty then continue
    let fields := (line.splitOn " ").filter (!·.isEmpty)
    let mut ns : Array Nat := #[]
    for field in fields do
      match field.toNat? with
      | some n => ns := ns.push n
      | none => throw (IO.userError "non-numeric trace field")
    if ns.size != 37 then throw (IO.userError "expected 37 trace fields")
    let stalls := ns[3]!
    let i : Input := {
      reset := ns[0]! != 0, valid := ns[1]! != 0, word := BitVec.ofNat 32 ns[2]!,
      stallFetch := stalls % 2 != 0, stallDecode := stalls / 2 % 2 != 0,
      stallExecute := stalls / 4 % 2 != 0, stallMemory := stalls / 8 % 2 != 0,
      stallWriteback := stalls / 16 % 2 != 0,
      initRegs := fun r => BitVec.ofNat 32 ns[5+r.toNat]! }
    let o := cycle s i
    let retired := o.retired.isSome
    let p := s.writeback.getD default
    let row : List Nat := if i.reset then List.replicate 9 0 else
      [if o.accepted then 1 else 0, if retired then 1 else 0,
       if retired then (encode p.instr).toNat else 0,
       if retired then s.arch.pc.toNat else 0,
       if retired then p.effect.value.toNat else 0,
       if retired then p.effect.rd.toNat else 0,
       s.arch.pc.toNat, (readReg s.arch (BitVec.ofNat 5 ns[4]!)).toNat, occupancy s]
    out.putStrLn (String.intercalate " " (row.map toString))
    s := o.state
end CaseCPU
def main (args : List String) : IO Unit := CaseCPU.traceMain args
