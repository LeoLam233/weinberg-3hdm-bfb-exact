#!/usr/bin/env python3
"""Fresh W3 kernel build, reusing only separately pinned dependency outputs.
No target W3 object is imported from the incremental W3 build. Every build
root is newly created and every compiler invocation uses the shared lock.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,re,subprocess,sys,shutil
W=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--entry',default='W3.Main');p.add_argument('--label',required=True);p.add_argument('--dry-run',action='store_true');p.add_argument('--all-local',action='store_true');a=p.parse_args()
def strip_comments(s):
 out=[];i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s[i:i+2]=='/-':depth+=1;i+=2
   elif s[i:i+2]=='-/':depth-=1;i+=2
   else:i+=1
  elif quoted:
   if s[i]=='\\':i+=2
   elif s[i]=='"':quoted=False;out.append('"');i+=1
   else:i+=1
  elif s[i:i+2]=='/-':depth=1;i+=2
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':quoted=True;out.append('"');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
seen=set();visiting=set();order=[];sources={};external=set()
def walk(m):
 if m in seen:return
 if m in visiting:raise RuntimeError('Import cycle '+m)
 if m!='W3' and not m.startswith('W3.'):
  external.add(m);return
 visiting.add(m);src=W/Path(m.replace('.','/')).with_suffix('.lean');raw=src.read_bytes();clean=strip_comments(raw.decode())
 bad=re.findall(r'\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|partial|ofReduceBool|ofReduceNat|trustCompiler)\b',clean)
 if 'debug.skipKernelTC' in clean:bad.append('debug.skipKernelTC')
 if bad:raise RuntimeError(f'Forbidden declaration/tactic tokens in {src}: {bad}')
 for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',clean,re.M):
  for dep in line.split():walk(dep)
 visiting.remove(m);seen.add(m);order.append(m);sources[m]={'source':str(src.relative_to(W)),'sha256':hashlib.sha256(raw).hexdigest()}
walk(a.entry)
if a.all_local:
 for src in sorted((W/'W3').glob('*.lean')):walk('W3.'+src.stem)
 if (W/'W3.lean').is_file():walk('W3')
plan={'entry':a.entry,'order':order,'sources':sources,'external_imports':sorted(external),'disk':dict(zip(('total','used','free'),shutil.disk_usage(W)))}
if a.dry_run:print(json.dumps(plan,indent=2));raise SystemExit()
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');root=W/'fresh'/f'{stamp}_{a.label}';build=root/'lib';logs=root/'logs';build.mkdir(parents=True);logs.mkdir()
(W/'.lake/build/lib/lean').mkdir(parents=True,exist_ok=True)
for child in (W/'.lake/build/lib/lean').iterdir():
 if child.name!='W3' and not child.name.startswith('W3.'):(build/child.name).symlink_to(child.resolve(),target_is_directory=child.is_dir())
(build/'W3').mkdir()
plan.update(utc=stamp,build_root=str(build),receipts=[],complete=False)
report=root/'BUILD.json';report.write_text(json.dumps(plan,indent=2));print('FRESH_ROOT',root,flush=True)
for m in order:
 src=W/sources[m]['source']
 if hashlib.sha256(src.read_bytes()).hexdigest()!=sources[m]['sha256']:raise RuntimeError('Source changed after freeze: '+m)
 out=build/Path(m.replace('.','/')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 assert not out.exists() and not out.is_symlink()
 ret=subprocess.run([sys.executable,str(W/'scripts/run_portable.py'),'--build-root',str(build),'--receipt-dir',str(logs),'--label',m.replace('.','_'),'--','-o',str(out),str(src.relative_to(W))]).returncode
 plan['receipts'].append({'module':m,'exit':ret,'output_sha256':hashlib.sha256(out.read_bytes()).hexdigest() if out.exists() else None});report.write_text(json.dumps(plan,indent=2))
 if ret:print('FRESH_FAILED',report);raise SystemExit(ret)
for m,s in sources.items():
 if hashlib.sha256((W/s['source']).read_bytes()).hexdigest()!=s['sha256']:raise RuntimeError('Source changed during build: '+m)
plan.update(complete=True,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());report.write_text(json.dumps(plan,indent=2));print('FRESH_SUCCESS',report)
