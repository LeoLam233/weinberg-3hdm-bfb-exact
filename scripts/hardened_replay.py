"""Fail-closed finite-evidence replay. This is not a theorem verifier.

Copy scientific code and declared input data only. Each suite output must be
absent immediately before execution and freshly created afterwards. Compare
JSON recursively with strict type matching and finite numerical values. Avoid
Python assert for acceptance decisions. Reject optimized interpreter mode.
"""
from __future__ import annotations
import argparse,hashlib,json,math,os,platform,shutil,subprocess,sys,tempfile,time
from pathlib import Path
EXACT=['exact_checks','closure_audit_checks','face_and_infinitesimal_checks','hexagon_spectrum_probe','final_destructive_checks','field_and_genericity_checks']
FLOATING=['hexagon_numeric','affine_shift_checks']
ALL=EXACT+FLOATING
SOURCE=Path(__file__).resolve().parents[1]/'research'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def compare(a,b,*,floating=False,path='root'):
 if type(a) is not type(b):raise ValueError(f'{path}: type mismatch {type(a).__name__} vs {type(b).__name__}')
 if isinstance(a,dict):
  if a.keys()!=b.keys():raise ValueError(f'{path}: key mismatch')
  for key in a:compare(a[key],b[key],floating=floating,path=f'{path}/{key}')
 elif isinstance(a,list):
  if len(a)!=len(b):raise ValueError(f'{path}: length mismatch')
  for i,(x,y) in enumerate(zip(a,b)):compare(x,y,floating=floating,path=f'{path}/{i}')
 elif type(a) in (int,float):
  if type(a) is float and (not math.isfinite(a) or not math.isfinite(b)):raise ValueError(f'{path}: nonfinite numeric value')
  if floating:
   if not math.isclose(a,b,rel_tol=1e-9,abs_tol=1e-10):raise ValueError(f'{path}: numeric mismatch')
  elif a!=b:raise ValueError(f'{path}: exact numeric mismatch')
 elif a!=b:raise ValueError(f'{path}: value mismatch')

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',type=Path,default=SOURCE);p.add_argument('--code-root',type=Path);p.add_argument('--output-dir',type=Path,required=True);p.add_argument('--suites',nargs='+',choices=ALL,default=ALL);p.add_argument('--timeout',type=int,default=120);args=p.parse_args()
 if sys.flags.optimize:raise RuntimeError('Run with assertion-enabled Python so captured scientific assertions execute')
 src=args.source.resolve();code=(args.code_root or src/'code').resolve();out=args.output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
 manifest={'scope':'finite evidence replay, not theorem proof','python':sys.version,'platform':platform.platform(),'code_sha256':{x.name:sha(x)for x in sorted(code.glob('*.py'))},'declared_inputs':{'results/duality_probe.json':sha(src/'results/duality_probe.json')},'expected_sha256':{f'{n}.json':sha(src/'results'/f'{n}.json')for n in args.suites},'checks':[]}
 env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
 status=0
 try:
  with tempfile.TemporaryDirectory(prefix='w3_hardened_',dir=out)as temp:
   work=Path(temp);shutil.copytree(code,work/'code',ignore=shutil.ignore_patterns('__pycache__'));(work/'results').mkdir()
   shutil.copy2(src/'results/duality_probe.json',work/'results/duality_probe.json')
   for name in args.suites:
    expected_file=src/'results'/f'{name}.json';new_file=work/'results'/f'{name}.json';cmd=[sys.executable,'-E','-B',str(work/'code'/f'{name}.py')]
    record={'suite':name,'command':cmd,'output_absent_before':not new_file.exists()};manifest['checks'].append(record)
    if new_file.exists():raise RuntimeError(f'{name}: output already exists before execution')
    start=time.monotonic()
    run=subprocess.run(cmd,cwd=work,env=env,capture_output=True,text=True,timeout=args.timeout)
    record.update(exit=run.returncode,elapsed_seconds=time.monotonic()-start)
    (out/f'{name}.stdout').write_text(run.stdout);(out/f'{name}.stderr').write_text(run.stderr)
    if run.returncode:raise RuntimeError(f'{name}: nonzero exit {run.returncode}')
    if not new_file.is_file()or new_file.is_symlink():raise RuntimeError(f'{name}: new regular output file missing')
    record['new_output_created']=True;record['new_sha256']=sha(new_file)
    # Retain fresh output even when comparison fails, for diagnosis.
    shutil.copy2(new_file,out/f'{name}.json')
    compare(json.loads(expected_file.read_text()),json.loads(new_file.read_text()),floating=name in FLOATING)
    record['status']='PASS';print(name+': PASS',flush=True)
 except Exception as exc:
  manifest['error']=str(exc);status=1;print('FAIL: '+str(exc),file=sys.stderr,flush=True)
 manifest['status']='PASS'if status==0 else'FAIL';(out/'receipt.json').write_text(json.dumps(manifest,indent=2));return status
if __name__=='__main__':sys.exit(main())
