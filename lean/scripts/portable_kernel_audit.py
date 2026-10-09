#!/usr/bin/env python3
"""Audit actual freshly built W3 kernel declarations and replay the pinned checker.
Same Lean kernel, not an external proof verifier. All failures remain recorded.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,subprocess,sys,os
W=Path(__file__).resolve().parents[1]
R=Path(os.environ.get('W3_DEPENDENCY_ROOT',str(W))).resolve()
p=argparse.ArgumentParser();p.add_argument('--build-report',type=Path,required=True);p.add_argument('--skip-checker',action='store_true');a=p.parse_args();a.build_report=a.build_report.resolve()
b=json.loads(a.build_report.read_text());assert b['complete'] is True
root=a.build_report.parent;build=Path(b['build_root']);out=root/('kernel_audit_'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));out.mkdir(exist_ok=False);gen=out/'generated';gen.mkdir();logs=out/'logs';logs.mkdir()
summary={'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entry':b['entry'],'audit_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'fresh_build_report_sha256':hashlib.sha256(a.build_report.read_bytes()).hexdigest(),'steps':[],'status':'RUNNING','limitations':['Uses the same Lean kernel, not an external independent verifier.','Pinned dependency artifacts are fingerprinted, not freshly rebuilt from source.','Trust-zero import alone is not evidence of explicit imported proof-body replay.','Pinned LeanChecker skips unsafe/partial runtime declarations; local W3 sources and declarations are separately gated.']}
report=out/'AUDIT.json'
def save():report.write_text(json.dumps(summary,indent=2))
def invoke(label,args,required=True):
 cmd=[sys.executable,str(W/'scripts/run_portable.py'),'--build-root',str(build),'--receipt-dir',str(logs),'--label',label,'--',*map(str,args)]
 r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(out/(label+'.txt')).write_text(r.stdout);print(label,r.returncode,flush=True)
 rs=sorted(logs.glob('*_'+label+'.result.json'));summary['steps'].append({'label':label,'exit':r.returncode,'receipt':str(rs[-1]) if rs else None});save()
 if r.returncode and required:raise RuntimeError(f'{label} failed; see retained output')
 return r
try:
 for m,s in b['sources'].items():
  assert hashlib.sha256((W/s['source']).read_bytes()).hexdigest()==s['sha256'],m+' changed'
 imports=''.join('import '+m+'\n' for m in b['order'])
 audit=gen/'AuditEnvironment.lean';audit.write_text(imports+(W/'scripts/AUDIT_BODY.txt').read_text())
 r=invoke('environment',['-R',gen,audit]);prefix='W3_AUDIT_JSON ';lines=[x[len(prefix):] for x in r.stdout.splitlines() if x.startswith(prefix)];assert len(lines)==1
 data=json.loads(lines[0]);(out/'environment.json').write_text(json.dumps(data,indent=2));ds=data['declarations'];assert ds
 allowed={'propext','Classical.choice','Quot.sound'}
 bad=[d for d in ds if d['unsafe'] or d['kind']=='axiom' or set(d['axioms'])-allowed]
 ax={'status':'FAIL' if bad else 'PASS','declarations':len(ds),'theorems':sum(d['kind']=='theorem' for d in ds),'allowed_standard_axioms':sorted(allowed),'violations':bad}
 (out/'axioms.json').write_text(json.dumps(ax,indent=2));assert not bad, 'axiom/unsafe violation'
 names={d['name'] for d in ds}
 for d in ds:d['local_dependencies']=sorted(set(d['type_dependencies']+d['value_dependencies'])&names)
 (out/'proof_dependency_graph.json').write_text(json.dumps({'relation':'constant names used by actual kernel types/proof bodies, not module imports','declarations':ds},indent=2))
 receipt=json.loads(Path(summary['steps'][-1]['receipt']).read_text());roots=[Path(x) for x in receipt['lean_path'].split(':')]+[R/'runtime/lean-4.34.1-linux/lib/lean'];fps={}
 for m in data['imported_modules']:
  rel=Path(m.replace('.','/')).with_suffix('.olean');f=next((r/rel for r in roots if (r/rel).is_file()),None)
  assert f is not None,m
  fps[m]=[{'path':str(x),'bytes':x.stat().st_size,'sha256':hashlib.sha256(x.read_bytes()).hexdigest()} for x in sorted(f.parent.glob(f.name+'*')) if x.is_file()]
 (out/'imported_artifact_hashes.json').write_text(json.dumps({'scope':'Available olean/private/server artifact identities, not a system-call read trace','modules':fps},indent=2))
 printer=gen/'PrintAxioms.lean';printer.write_text(imports+(W/'scripts/PRINT_AXIOMS_BODY.txt').read_text());invoke('print_axioms',['-R',gen,printer])
 probe=gen/'TrustZero.lean';probe.write_text('theorem zero_eq_zero : (0 : Nat) = 0 := rfl\n');invoke('trust_zero_probe',['-t0','-R',gen,probe])
 aggregate=gen/'W3KernelAggregate.lean';aggregate.write_text(imports);invoke('trust_zero_aggregate',['-t0','-R',gen,'-o',build/'W3KernelAggregate.olean',aggregate])
 if not a.skip_checker:
  checker=R/'runtime/lean-4.34.1-linux/src/lean/LeanChecker.lean';summary['checker_source_sha256']=hashlib.sha256(checker.read_bytes()).hexdigest()
  c=invoke('leanchecker_fresh',['--run',checker,'--fresh','W3KernelAggregate'],required=False)
  summary['fresh_checker_status']='PASS' if c.returncode==0 else 'FAIL'
  if c.returncode:
   summary['fallback_scope']='local modules replayed individually against imported environments; full fresh replay failed'
   for m in b['order']:invoke('leanchecker_'+m.replace('.','_'),['--run',checker,m])
   raise RuntimeError('Full fresh LeanChecker failed; narrower fallback does not satisfy the full replay gate')
 else:summary['fresh_checker_status']='NOT_RUN'
 for m,s in b['sources'].items():assert hashlib.sha256((W/s['source']).read_bytes()).hexdigest()==s['sha256'],m+' changed'
 summary['status']='PASS' if summary['fresh_checker_status']=='PASS' else 'PARTIAL_CHECKER_NOT_RUN';summary['finished']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();print('AUDIT_REPORT',report)
except BaseException as e:
 summary['status']='FAIL';summary['error']=repr(e);save();raise
