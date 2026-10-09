import pathlib, re, subprocess, sys
b=pathlib.Path(__file__).resolve().parents[1];m=b/'.lake/packages/mathlib';out=m/'.lake/build/lib/lean';seen=set()
def build(name):
 if name in seen:return
 seen.add(name)
 if not name.startswith(('Cache.','Batteries.')):return
 pkg=m if name.startswith('Cache.') else b/'.lake/packages/batteries'
 src=pkg/(name.replace('.','/')+'.lean')
 for dep in re.findall(r'^import\s+([\w.]+)',src.read_text(),re.M):build(dep)
 dest=pkg/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run([sys.executable,str(b/'scripts/run_portable.py'),'--cwd',str(pkg),'--label',name,'--','-o',str(dest),str(src)])
 if r.returncode:raise SystemExit(r.returncode)
build('Cache.Main')
