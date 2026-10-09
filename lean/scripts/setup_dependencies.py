#!/usr/bin/env python3
"""Restore exact official dependency archives without Lake update or any Ising input.

Default verifies manifest/receipt agreement only. --verify-installed additionally
verifies every source-archive hash and every archived source file already installed.
--install downloads missing archives and installs only absent/empty vendor trees.
--runtime applies the same explicit restoration to the pinned Linux x86-64 runtime.
"""
import argparse, datetime, hashlib, json, os, shutil, tarfile, tempfile, urllib.request
from pathlib import Path, PurePosixPath
ROOT=Path(__file__).resolve().parents[1]
RUNTIME_URL='https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst'
RUNTIME_SHA='47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4'

def sha(path):
    with path.open('rb') as f: return hashlib.file_digest(f,'sha256').hexdigest()

def check_hash(path, expected):
    got=sha(path)
    if got!=expected: raise RuntimeError(f'Hash mismatch: {path}: {got} != {expected}')
    return got

def fetch(path,url,expected):
    if not path.exists():
        path.parent.mkdir(parents=True,exist_ok=True)
        temporary=path.with_name(path.name+'.download')
        with urllib.request.urlopen(url,timeout=180) as r,temporary.open('xb') as f: shutil.copyfileobj(r,f)
        check_hash(temporary,expected); temporary.rename(path)
    return check_hash(path,expected)

def members(t):
    for member in t:
        parts=PurePosixPath(member.name).parts
        if not parts or PurePosixPath(member.name).is_absolute() or '..' in parts: raise RuntimeError('Unsafe archive path')
        if len(parts)>1:
            member.name='/'.join(parts[1:]); yield member

def check_sources(archive,dest):
    checked=0
    with tarfile.open(archive,'r:gz') as t:
        for m in members(t):
            path=dest/m.name
            if m.isfile():
                if not path.is_file(): raise RuntimeError(f'Missing source file: {path}')
                with t.extractfile(m) as f: expected=hashlib.file_digest(f,'sha256').hexdigest()
                check_hash(path,expected); checked+=1
            elif m.issym():
                if not path.is_symlink() or os.readlink(path)!=m.linkname: raise RuntimeError(f'Changed source symlink: {path}')
    return checked

def install_source(archive,dest):
    if dest.exists() and any(dest.iterdir()): raise RuntimeError(f'Refusing to overwrite nonempty vendor tree {dest}; use --verify-installed')
    dest.mkdir(parents=True,exist_ok=True)
    with tarfile.open(archive,'r:gz') as t:
        for m in members(t): t.extract(m,dest,filter='data')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--verify-installed',action='store_true')
    p.add_argument('--install',action='store_true')
    p.add_argument('--runtime',action='store_true')
    p.add_argument('--receipt-out',type=Path)
    a=p.parse_args(); out=a.receipt_out or ROOT/'logs'/('setup_'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')+'.json')
    out.parent.mkdir(parents=True,exist_ok=True)
    report={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'RUNNING','operation':vars(a)|{'receipt_out':str(out)},'dependencies':[]}
    try:
        manifest=json.loads((ROOT/'lake-manifest.json').read_text())
        receipts=json.loads((ROOT/'recovery/dependency_source_receipt.json').read_text()); rs={r['name']:r for r in receipts}
        if set(rs)!={p['name'] for p in manifest['packages']}: raise RuntimeError('Manifest and archive receipt package sets differ')
        for entry in manifest['packages']:
            r=rs[entry['name']]; expected_url=entry['url'].removesuffix('.git').replace('https://github.com/','https://codeload.github.com/')+'/tar.gz/'+entry['rev']
            if r['rev']!=entry['rev'] or r['url']!=expected_url: raise RuntimeError('Manifest and archive source pin mismatch')
            archive=ROOT/'recovery'/(r['name']+'-'+r['rev']+'.tar.gz'); dest=ROOT/'.lake/packages'/r['name']
            record={**r,'manifest_agrees':True}
            if a.install: fetch(archive,r['url'],r['archive_sha256']); install_source(archive,dest)
            if a.install or a.verify_installed:
                record['verified_archive_sha256']=check_hash(archive,r['archive_sha256'])
                record['verified_source_files']=check_sources(archive,dest)
            report['dependencies'].append(record)
        if a.runtime:
            archive=ROOT/'recovery/runtime_archive'; dest=ROOT/'runtime/lean-4.34.1-linux'
            if a.install:
                fetch(archive,RUNTIME_URL,RUNTIME_SHA)
                if dest.exists(): raise RuntimeError('Refusing to overwrite installed runtime; use --verify-installed --runtime')
                try: import zstandard
                except ImportError as e: raise RuntimeError('Install the conventional PyPI zstandard dependency in your chosen Python environment to extract the official .tar.zst runtime.') from e
                dest.parent.mkdir(parents=True,exist_ok=True)
                with archive.open('rb') as src,zstandard.ZstdDecompressor().stream_reader(src) as raw,tarfile.open(fileobj=raw,mode='r|') as t:
                    for m in t:
                        parts=PurePosixPath(m.name).parts
                        if not parts or parts[0]!='lean-4.34.1-linux' or '..' in parts or PurePosixPath(m.name).is_absolute(): raise RuntimeError('Unsafe runtime archive path')
                        t.extract(m,dest.parent,filter='data')
            report['runtime']={'url':RUNTIME_URL,'archive_sha256':check_hash(archive,RUNTIME_SHA),'installed_lean_sha256':sha(dest/'bin/lean'),'scope':'Exact official runtime archive verified; installed executable fingerprinted. Full runtime extraction is not compared byte by byte.'}
        report['status']='PASS'
    except BaseException as e:
        report['status']='FAIL'; report['failure']=f'{type(e).__name__}: {e}'
    report['ended_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat(); out.write_text(json.dumps(report,indent=2,default=str)+'\n')
    print(json.dumps({'status':report['status'],'receipt':str(out),'failure':report.get('failure')})); return 0 if report['status']=='PASS' else 1
if __name__=='__main__': raise SystemExit(main())
