"""Fixed model audit and post-proof emission, without any HDL roundtrip."""
import json
from pathlib import Path
import shutil
import refinement_checks as checks


def validate(ws, logdir, expected=None):
    ws,logdir=Path(ws),Path(logdir)
    (ws/'StructureCheck.lean').write_text('import FrozenContract\nimport Imported\n'
        'set_option maxHeartbeats 16000000\nset_option maxRecDepth 32768\n'
        'example : FrozenContract.valid V2LeanImported.impl = true := by decide +kernel\n')
    for args,name in [(['lake','build','Imported','FrozenContract'],'structure-build'),
                      (['lake','env','lean','StructureCheck.lean'],'structure-check')]:
        result=checks.run(ws,args,logdir,name)
        if not result['ok']:return result
    contract=json.loads((ws/'contract.json').read_text())
    return {'ok':True,'contract_sha256':checks.sha(ws/'FrozenContract.lean'),
            'signature':contract['ports'],'parameter_scope':'benchmark_defaults'}


def emit(ws, out):
    ws,out=Path(ws),Path(out)
    out.mkdir(parents=True,exist_ok=False)
    contract=json.loads((ws/'contract.json').read_text())
    kind,top=contract['model_kind'],contract['top']
    source='import Lean\nimport Imported\ndef main : IO Unit := do\n'
    if kind=='symbolic':
        source+='  let m := V2LeanImported.impl\n'
        source+='  IO.FS.writeFile "emit.rtlil.json" m.core.interfaceCore.toRtlilJson\n'
        source+='  IO.FS.writeFile "emit.wrapper.v" m.core.interfaceWrapper\n'
        source+='  IO.FS.writeFile "emit.choices.json" (Lean.toJson (m.choices.map fun p => (p.name,p.width))).compress\n'
    else:
        body={'clocked':'V2LeanImported.impl.emit',
              'fourstate':'LeanRTL.FourState.Verilog.emit V2LeanImported.impl',
              'timed':'LeanRTL.FourState.Timed.emit '+json.dumps(top)+' V2LeanImported.impl'}[kind]
        source+='  IO.FS.writeFile "emit.final.v" ('+body+')\n'
    (ws/'TrustedEmit.lean').write_text(source)
    r=checks.run(ws,['lake','env','lean','-s','65536','--run','TrustedEmit.lean'],out,'emit-lean')
    if not r['ok']:return r
    if kind=='symbolic':
        (ws/'emit.ys').write_text('read_json emit.rtlil.json\ncheck -assert\nwrite_verilog -noattr emit.core.v\n')
        r=checks.run(ws,['yosys','-Q','-T','-s','emit.ys'],out,'emit-yosys')
        if not r['ok']:return r
        text=(ws/'emit.core.v').read_text()+'\n'+(ws/'emit.wrapper.v').read_text()
        choices=json.loads((ws/'emit.choices.json').read_text())
        if choices:
            (ws/'emit.base.v').write_text(text)
            internal=top+'__symbolic_implementation'
            (ws/'emit.rename.ys').write_text('read_verilog -sv emit.base.v\n'
                f'hierarchy -check -top {top}\nrename {top} {internal}\nwrite_verilog -noattr emit.internal.v\n')
            r=checks.run(ws,['yosys','-Q','-T','-s','emit.rename.ys'],out,'emit-internal')
            if not r['ok']:return r
            ports={n:contract['ports'][n] for n in contract['port_order']}
            wrapper=['module '+top+'('+', '.join(ports)+');']
            for n,p in ports.items():
                width=len(p['bits']);lo=p.get('offset',0);hi=lo+width-1
                bounds=f'[{lo}:{hi}]' if p.get('upto') else f'[{hi}:{lo}]'
                wrapper.append(p['direction']+' wire '+('signed ' if p.get('signed') else '')+bounds+' '+n+';')
            connects=['.'+n+'('+n+')' for n in ports]
            connects += ['.'+n+f"({w}'bx)" for n,w in choices]
            wrapper += [internal+' dut('+', '.join(connects)+');','endmodule','']
            text=(ws/'emit.internal.v').read_text()+'\n'+'\n'.join(wrapper)
        (ws/'emit.final.v').write_text(text)
    r=checks.run(ws,['iverilog','-g2012','-s',top,'-o','emit.syntax.vvp','emit.final.v'],out,'syntax')
    if not r['ok']:return r
    final=out/'final.v';shutil.copy2(ws/'emit.final.v',final)
    result={'ok':True,'final_path':str(final),'final_sha256':checks.sha(final),
            'source_impl_sha256':checks.sha(ws/'Imported.lean'),
            'kind':kind,'roundtrip':False,'jasper':False,'parameter_scope':'benchmark_defaults'}
    checks.save(out/'result.json',result)
    return result
