#!/usr/bin/env python3
"""One project-wide compiler process, one Lean worker, isolated paths, complete receipts."""
import argparse, datetime, fcntl, hashlib, json, os, pathlib, resource, subprocess, sys, time
WORK=pathlib.Path(__file__).resolve().parents[1]
ROOT=pathlib.Path(os.environ.get('W3_DEPENDENCY_ROOT',str(WORK))).resolve()
RUNTIME=ROOT/'runtime/lean-4.34.1-linux/bin'
def snapshot():
 out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'disk':dict(zip(('total','used','free'),__import__('shutil').disk_usage(ROOT)))}
 for p in ['/proc/meminfo','/proc/self/cgroup','/sys/fs/cgroup/memory.max','/sys/fs/cgroup/memory.current','/sys/fs/cgroup/memory.peak','/sys/fs/cgroup/memory.events']:
  try:out[p]=pathlib.Path(p).read_text()
  except OSError as e:out[p]={'unavailable':str(e)}
 return out
p=argparse.ArgumentParser();p.add_argument('--cwd',type=pathlib.Path,default=WORK);p.add_argument('--label',default='lean');p.add_argument('--build-root',type=pathlib.Path,default=WORK/'.lake/build/lib/lean');p.add_argument('--receipt-dir',type=pathlib.Path,default=WORK/'logs');p.add_argument('args',nargs=argparse.REMAINDER);a=p.parse_args();args=a.args
if args and args[0]=='--':args=args[1:]
if any(x.startswith(('-j','--threads','-M','--memory')) for x in args):raise SystemExit('Thread/memory settings are owned by wrapper; initial -j1 -M4096')
a.receipt_dir=a.receipt_dir.resolve();a.receipt_dir.mkdir(parents=True,exist_ok=True);a.build_root=a.build_root.resolve();a.cwd=a.cwd.resolve()
lock_path=ROOT/'coordination/lean.lock'
if ROOT==WORK:
 lock_path.parent.mkdir(parents=True,exist_ok=True)
 lock_path.touch(exist_ok=True)
if not lock_path.is_file():raise SystemExit('External dependency root must supply its existing shared coordination/lean.lock')
with lock_path.open('rb') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'); stem=a.receipt_dir/f'{stamp}_{a.label}'
 env=os.environ.copy();env['PATH']=str(RUNTIME)+':'+env['PATH'];paths=[a.build_root]; sources=[WORK]
 for pkg in sorted((ROOT/'.lake/packages').iterdir()):
  if pkg.is_dir(): paths.append(pkg/'.lake/build/lib/lean'); sources.append(pkg)
 nested=ROOT/'.lake/packages/mathlib/.lake/packages'
 if nested.exists(): paths = [a.build_root] + [pkg/'.lake/build/lib/lean' for pkg in sorted(nested.iterdir()) if pkg.is_dir()] + paths[1:]
 env['LEAN_PATH']=':'.join(str(x) for x in paths);env['LEAN_SRC_PATH']=':'.join(str(x) for x in sources);env['MATHLIB_CACHE_DIR']=str(ROOT/'.cache/mathlib');env['LAKE_JOBS']='1';env['OMP_NUM_THREADS']='1'
 cmd=[str(RUNTIME/'lean'),'-j1','-M4096',*args]; before=snapshot();start=time.monotonic()
 src=[]
 for arg in args:
  x=a.cwd/arg
  if x.is_file():src.append({'path':str(x),'sha256':hashlib.sha256(x.read_bytes()).hexdigest()})
 receipt={'command':cmd,'cwd':str(a.cwd),'before':before,'lean_path':env['LEAN_PATH'],'lean_src_path':env['LEAN_SRC_PATH'],'build_root':str(a.build_root),'compiler_sha256':hashlib.sha256((RUNTIME/'lean').read_bytes()).hexdigest(),'wrapper_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'source_inputs':src,'internal_threads':1,'lean_memory_cap_mib':4096,'cgroup_limit_status':'Unavailable if not exposed; see snapshot, never inferred from MemTotal'}
 stem.with_suffix('.command.json').write_text(json.dumps(receipt,indent=2))
 with stem.with_suffix('.stdout.txt').open('wb') as so,stem.with_suffix('.stderr.txt').open('wb') as se:
  proc=subprocess.Popen(cmd,cwd=a.cwd,env=env,stdout=so,stderr=se);_,status,usage=os.wait4(proc.pid,0);ret=os.waitstatus_to_exitcode(status);proc.returncode=ret
 receipt.update(exit_code=ret,elapsed_seconds=time.monotonic()-start,maxrss_kib=usage.ru_maxrss,user_seconds=usage.ru_utime,system_seconds=usage.ru_stime,after=snapshot(),metric_source='os.wait4 rusage; /usr/bin/time absent')
 stem.with_suffix('.result.json').write_text(json.dumps(receipt,indent=2))
 print(stem.with_suffix('.stdout.txt').read_text(),end='');print(stem.with_suffix('.stderr.txt').read_text(),end='',file=sys.stderr);print(f'LEAN_RESULT {ret} maxrss_kib={usage.ru_maxrss} receipt={stem.with_suffix(".result.json")}',file=sys.stderr)
 sys.exit(ret)
