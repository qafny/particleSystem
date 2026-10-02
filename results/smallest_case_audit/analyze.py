"""One-input diagnostic; does not modify benchmark runners or result CSVs."""
import os
os.environ.setdefault('MPLCONFIGDIR','/tmp/qblue-plot-cache')
import sys,json,hashlib,math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'thirdparty/OpenFermion/src'))
sys.path.insert(0,str(ROOT/'scripts'))
import numpy as np
from scipy.linalg import expm
from qiskit import QuantumCircuit,transpile
from qiskit.quantum_info import Operator,SparsePauliOp
from openfermion import QubitOperator,trotterize_exp_qubop_to_qasm
from openfermion.circuits.trotter.trotter_error import error_bound
from openfermion_bench import parse_hamiltonian,gate_counts
OUT=Path(__file__).resolve().parent
path=ROOT/'mlqblue/DataSet1/small/MarqSim_Ar_60.txt'
terms=parse_hamiltonian(path);t=.7854;eps=.1;r=1768
op=QubitOperator()
for label,c in terms: op+=QubitOperator(tuple((i,p) for i,p in enumerate(label) if p!='I'),c)
order=sorted(op.terms)
file_order=[tuple((i,p) for i,p in enumerate(label) if p!='I') for label,c in terms]
H=SparsePauliOp([p[::-1] for p,c in terms],[c for p,c in terms]).to_matrix()
exact=expm(-1j*t*H)
def errors(u,v):
 phase=np.angle(np.vdot(v,u))
 return {'spectral_error':float(np.linalg.norm(u-v,2)), 'phase_aligned_spectral_error':float(np.linalg.norm(u*np.exp(-1j*phase)-v,2))}
def ideal_step(seq,steps):
 u=np.eye(256,dtype=complex)
 for term in seq:
  label=['I']*8
  for i,p in term: label[7-i]=p
  P=SparsePauliOp([''.join(label)]).to_matrix()
  angle=t*op.terms[term]/(2*steps)
  u=np.cos(angle)*u-1j*np.sin(angle)*(P@u)
 return u
report={'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'terms':len(terms),'nqubit':8,
 'max_abs_coefficient':max(abs(c) for p,c in terms),'sum_abs_coefficients':sum(abs(c) for p,c in terms),
 'bound_coefficient':error_bound([QubitOperator(p,op.terms[p]) for p in reversed(order)],tight=True),'cases':{}}
qseq=list(reversed(file_order))+file_order
oseq=order+list(reversed(order))
for steps in [1,r]:
 qideal=ideal_step(qseq,steps); oideal=ideal_step(oseq,steps)
 for label,u in [('qblue_ideal',qideal),('openfermion_ideal',oideal)]:
  e=errors(np.linalg.matrix_power(u,steps),exact)
  report['cases'][f'{label}_r{steps}']=e;print(label,steps,e,flush=True)
 if steps==r:
  u=Operator(QuantumCircuit.from_qasm_file(str(OUT/'qblue_actual_after.qasm'))).data
  report['cases']['qblue_actual_after_step_vs_ideal_no_layout_correction']=errors(u,qideal)
  report['cases']['qblue_actual_after_repeated_vs_exact_no_layout_correction']=errors(np.linalg.matrix_power(u,steps),exact)
# Reproduce actual OpenFermion runner for r=1; aligned-order control uses reversed file order.
for label,ordering in [('sorted',order),('qblue_order',list(reversed(file_order)))]:
 qc=QuantumCircuit(8)
 for line in trotterize_exp_qubop_to_qasm(op,evolution_time=t,trotter_number=1,trotter_order=2,term_ordering=ordering):
  p=line.split();g=p[0]
  if g=='H': qc.h(int(p[1]))
  elif g=='Rx': qc.rx(float(p[1]),int(p[2]))
  elif g=='Rz': qc.rz(float(p[1]),int(p[2]))
  elif g=='CNOT': qc.cx(int(p[1]),int(p[2]))
 before=transpile(qc,basis_gates=['u1','u2','u3','cx'],optimization_level=0,seed_transpiler=0)
 after=transpile(before,basis_gates=['u1','u2','u3','cx'],optimization_level=3,seed_transpiler=0)
 report[label]={'before_1q_cx':gate_counts(before),'after_1q_cx':gate_counts(after),
 'actual_error':errors(Operator(after).data,exact),
 'vs_ideal_step':errors(Operator(qc).data,ideal_step(ordering+list(reversed(ordering)),1))}
(OUT/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
