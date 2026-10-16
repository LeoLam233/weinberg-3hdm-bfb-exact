from pathlib import Path
import sympy as sp, hashlib,json,re,subprocess
r=Path(__file__).resolve().parents[2]; out=Path(__file__).resolve().parent
original=(r/'research/THEOREM.md').read_text()
revised=(out/'THEOREM_REVISED.md').read_text()
assert re.findall(r'\\tag\{(\d+)\}',original)==re.findall(r'\\tag\{(\d+)\}',revised)
assert original[original.index('[BPR06] S.'):original.index('The current-open')]==revised[revised.index('[BPR06] S.'):revised.index('The source and bounded')]
t,u=sp.symbols('t u')
F=-3365*t*t*u*u-14400*t*t*u+2321*t*t+10020*t*u*u-7612*t*u-3060*t+1485*u*u-1320*u-441
G=-20735*t*t*u*u-44520*t*t*u+4613*t*t+96460*t*u*u-49896*t*u+10780*t+20335*u*u+41160*u-4213
P=65532894182001*t**6-846134370496944*t**5+2404104611159391*t**4+2245261288159824*t**3-463362875655073*t**2-249992387249952*t-20785328196111
res=sp.resultant(F,G,u)
assert sp.expand(res-100*(1+t*t)*P)==0
assert sp.gcd(F,G)==1
assert sp.Poly(P,t).content()==1
# Off-support identity is symbolic: diagonal mixing is arbitrary, multiplied by z_i.
mix,zj,zk=sp.symbols('mix zj zk'); zi=sp.Integer(0)
assert sp.expand(mix*zi+zi*zj*zj+zi*zk*zk)==0
targets={
'W3.Infinitesimal.actualParameters_generic':'ActualGenericity.lean',
'W3.Operator.inverse_projector_zero_component':'OperatorConcrete.lean',
'W3.FiniteInput.uniform_finite_input_exact_criterion':'FiniteInputMain.lean',
'W3.FiniteInput.arbitrary_complex_finite_input_criterion':'FiniteInputMain.lean',
'W3.FiniteInput.actualCodeProgram_values':'FiniteInputActualProgram.lean',
'W3.FiniteInput.actualCodeProgram_physical':'FiniteInputActualProgram.lean',
'W3.FiniteInput.actualSelectedRecord_value':'FiniteInputActualProgram.lean',
'W3.FiniteInput.actualValueCode_success':'FiniteInputActualProgram.lean',
'W3.FiniteInput.actualMatrixCode_spec':'FiniteInputActualProgram.lean',
'W3.FiniteInput.actualFields_spec':'FiniteInputActualProgram.lean',
'W3.FiniteInput.signPrograms_spec':'FiniteInputMain.lean',
'W3.FiniteInput.codedResidueStageProgram_correct':'FiniteInputResidueExecution.lean',
'W3.FiniteInput.every_old_retained_minimizer_coded_execution':'FiniteInputRetainedExecution.lean'}
declarations=[]
for name,f in targets.items():
 p=r/'lean/W3'/f; text=p.read_text(); short=name.split('.')[-1]
 match=re.search(r'^theorem '+short+r'\b',text,re.M);assert match,name
 declarations.append({'declaration':name,'path':str(p.relative_to(r)),'line':text[:match.start()].count('\n')+1,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
protected=[]
for area in ['research','lean','verification','docs']:
 for p in sorted((r/area).rglob('*')):
  if p.is_file() and out not in p.parents:
   rel=str(p.relative_to(r))
   old=subprocess.check_output(['git','-C',str(r),'show','5485acb93e9a6dc0631573c07a10e1666b23ca99:'+rel])
   assert old==p.read_bytes(),rel
   protected.append({'path':rel,'sha256':hashlib.sha256(old).hexdigest()})
result={'base_commit':subprocess.check_output(['git','-C',str(r),'rev-parse','5485acb93e9a6dc0631573c07a10e1666b23ca99']).decode().strip(),'checks':{'ordinary_resultant_equals_100_times_primitive_quotient':True,'gcd_F_G_is_one':True,'displayed_polynomial_is_primitive':True,'corrected_off_support_identity':True,'referenced_declarations_located':True,'original_tracked_sources_unchanged':True},'validation_scope':'Exact SymPy arithmetic and source-level manuscript concordance. No fresh Lean build/kernel replay or independent scientific audit performed for this editorial revision.','declarations':declarations,'protected_files':protected}
(out/'REVISION_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['checks'],indent=2));print('Protected files:',len(protected))
