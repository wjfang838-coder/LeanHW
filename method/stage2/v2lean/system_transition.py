"""Compare all four-state pending register values and observations of actual HDL.

This is a stronger diagnostic than selected traces: no state/input constraints
are imposed. Matching pending values plus corresponding process edge predicates
is the obligation needed for a temporal proof. HDL elaboration/reflection and
serialization remain explicit boundaries; this does not promote corpus status.
"""
import argparse
import json
from pathlib import Path
import re
import shutil

from .clocked_case import compile_model
from .importer import require
from .pipeline import ROOT, digest, run, save_json
from .system import SystemImporter
from .dag import deduplicate, render_checked


def encode(source, top, out):
    out.mkdir()
    shutil.copyfile(source, out/'input.v')
    importer=SystemImporter(out/'input.v',top)
    importer.build()
    save_json(out/'source.json',importer.metadata)
    text='import LeanRTL.Core.FourStateTransition\nimport LeanRTL.Core.FourStateDAG\n'+importer.model_text
    text+='\ndef raw_transition := impl.lower.transition\n'
    text+='def dag_input := DAG.expose raw_transition "_transition_output_"\n'
    generator=text+'''
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => IO.FS.writeFile path (DAG.candidateJson dag_input).compress; return 0
  | _ => throw (IO.userError "usage: BLOCKS_JSON")
'''
    (out/'Generator.lean').write_text(generator)
    generated_certificate=compile_model(out,'Generator.lean','dag_generator',importer)
    run([str(out/'dag_generator'),str(out/'blocks.raw.json')],out,out/'generate.log',timeout=300)
    save_json(out/'generator_certificate.json',generated_certificate)
    # Reserve physical names even when unused in every expression, plus the
    # separate external inout drives and old-state inputs of the transition.
    reserved_names=list(importer.ports)+['__external_'+n for n in importer.inout_names]
    reserved_names += [r['name'] for r in importer.metadata['states']]
    blocks,statistics=deduplicate(json.loads((out/'blocks.raw.json').read_text()),reserved_names)
    save_json(out/'blocks.shared.json',blocks)
    save_json(out/'dag_statistics.json',statistics)
    (out/'blocks.leaninc').write_text(render_checked(blocks))
    text+=(out/'blocks.leaninc').read_text()
    text+='''
def transition := DAG.expanded dag_input dag_blocks
theorem transition_dag_correct (env : Env) : transition.eval env = raw_transition.eval env := by
  have h := DAG.expanded_correct dag_input dag_blocks (by source_kernel_rfl)
    (by decide +kernel) (by decide +kernel) env
  have ho := DAG.expose_correct raw_transition "_transition_output_"
    (by decide +kernel) (by decide +kernel) (by decide +kernel) env
  exact h.trans ho
theorem transition_valid : transition.valid = true := by decide +kernel
theorem encoding_valid : Encoding.encodingValid transition = true := by decide +kernel
example : (Encoding.module transition).checkErrors = [] := by
  rw [← LeanRTL.Module.checkErrorsMap_eq]
  decide +kernel
theorem transition_semantics (state : NBA.Snapshot) (input : Env) :
  transition.eval (valuesEnv state input) =
    let read := valuesEnv (impl.lower.wireSnapshot state input) input
    impl.states.map (fun reg => ("next__" ++ reg.name, renderValue (impl.lower.pendingValue reg read))) ++
    impl.network.outputWires.map (fun o => ("out__" ++ o.name, renderValue (eval o.expr read))) := by
  rw [transition_dag_correct]
  exact NBA.transition_eval_correct _ _ _
theorem transition_encoding_correct (env : LeanRTL.Env) :
  Encoding.decodeOutputPairs transition.outputs
    ((Encoding.module transition).outputs?eval (fun _ => 0) env) =
    some (transition.eval (Encoding.decodedEnv env)) :=
  Encoding.module_correct_decoded transition encoding_valid env
#print axioms transition_semantics
#print axioms transition_encoding_correct
#print axioms transition_dag_correct
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => IO.FS.writeFile path (Encoding.module transition).toRtlilJson; return 0
  | _ => throw (IO.userError "usage: OUTPUT_JSON")
'''
    (out/'Imported.lean').write_text(text)
    certificate=compile_model(out,'Imported.lean','encode_model',importer)
    log=(out/'encode_model.kernel.log').read_text()
    audited={}
    for name in ('transition_semantics','transition_encoding_correct','transition_dag_correct'):
        matches=re.findall("'"+name+r"' depends on axioms: \[([^\]]*)\]",log,re.S)
        require(len(matches)==1,'missing transition proof audit: '+name)
        axioms={a.strip() for a in matches[0].split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'},'untrusted transition axiom')
        audited[name]=sorted(axioms)
    run([str(out/'encode_model'),str(out/'encoded.json')],out,out/'encode.log',timeout=300)
    certificate.update(transition_theorems=audited,encoded_json_hash=digest(out/'encoded.json'))
    save_json(out/'certificate.json',certificate)
    encoded=json.loads((out/'encoded.json').read_text())['modules'][top+'_transition_fourstate']
    for cell in encoded['cells'].values():
        for bits in cell['connections'].values():
            require(all(type(b) is int or b in ('0','1') for b in bits),'nonbinary transition encoding')
    (out/'emit.ys').write_text('read_json encoded.json\ncheck -assert\nopt_clean\nwrite_verilog -noattr encoded.v\n')
    run(['yosys','-Q','-T','-s','emit.ys'],out,out/'emit.log',timeout=300)
    ownership=[{'events':events,'targets':targets} for events,targets,_ in importer.nba_processes]
    return {'ports':importer.ports,'states':importer.metadata['states'],'processes':ownership}


def compare(case,out):
    case,out=Path(case).resolve(),Path(out).resolve()
    report=json.loads((case/'result.json').read_text())
    require(report['status']=='clocked_trace_diagnostic_pass' and report['frontend']=='system',
            'requires successful actual system traces')
    require(all(digest(case/n)==h for n,h in report['artifact_hashes'].items()),'case artifact changed')
    require(not out.exists(),'preserve prior transition evidence')
    out.mkdir()
    hashes={str(p.relative_to(ROOT)):digest(p) for p in (ROOT/'method/stage2/framework').rglob('*.lean')}
    hashes.update({str(p.relative_to(ROOT)):digest(p) for p in (ROOT/'method/stage2/v2lean').glob('*.py')})
    for n in hashes:
        dest=out/'source'/n;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/n,dest)
    top=next(iter(json.loads((case/'source.json').read_text())['modules']))
    run(['lake','build','LeanRTL:static'],ROOT,out/'build.log',timeout=300)
    gold=encode(case/'original.v',top,out/'gold')
    gate=encode(case/'emitted.v',top,out/'gate')
    require(gold==gate,'physical inputs, state correspondence, or event ownership changed')
    save_json(out/'correspondence.json',gold)
    (out/'miter.ys').write_text(f'''read_verilog gold/encoded.v
rename {top}_transition_fourstate gold
read_verilog gate/encoded.v
rename {top}_transition_fourstate gate
miter -equiv -flatten gold gate miter
hierarchy -check -top miter
proc
opt -full
check -assert
sat -verify -prove trigger 0 -show-inputs -show-outputs -dump_json cex.json
''')
    sat=run(['yosys','-Q','-T','-s','miter.ys'],out,out/'miter.log',timeout=300,check=False)
    passed=sat.returncode==0 and 'SAT proof finished - no model found: SUCCESS!' in sat.stdout
    unchanged=all(digest(ROOT/n)==h for n,h in hashes.items())
    result={'status':'fourstate_transition_diagnostic_pass' if passed and unchanged else 'failed',
            'sat_pass':passed,'state_bits':sum(r['width'] for r in gold['states']),
            'scope':'all four-state input and corresponding state encodings; every pending register value and physical observation; identical event ownership checked; no input assumptions',
            'limitations':'HDL elaboration/reflection and encoding serialization remain frontend/backend boundaries; no corpus promotion or whole-Verilog temporal certificate',
            'source_case':str(case),'source_case_result_hash':digest(case/'result.json'),
            'sources_unchanged':unchanged,'source_hashes':hashes,
            'artifact_hashes':{str(p.relative_to(out)):digest(p) for p in out.rglob('*') if p.is_file() and 'source' not in p.relative_to(out).parts}}
    save_json(out/'result.json',result)
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('case',type=Path);parser.add_argument('out',type=Path)
    args=parser.parse_args()
    result=compare(args.case,args.out)
    print(json.dumps({k:result[k] for k in ('status','state_bits','sat_pass')}))
    raise SystemExit(0 if result['status']=='fourstate_transition_diagnostic_pass' else 1)
