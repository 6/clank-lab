/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk80 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (10240+j)))
theorem checkChunk80_pass : checkChunk80 = true := by decide
#print axioms checkChunk80_pass
def checkChunk81 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (10368+j)))
theorem checkChunk81_pass : checkChunk81 = true := by decide
#print axioms checkChunk81_pass
def checkChunk82 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (10496+j)))
theorem checkChunk82_pass : checkChunk82 = true := by decide
#print axioms checkChunk82_pass
def checkChunk83 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (10624+j)))
theorem checkChunk83_pass : checkChunk83 = true := by decide
#print axioms checkChunk83_pass
def checkChunk84 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (10752+j)))
theorem checkChunk84_pass : checkChunk84 = true := by decide
#print axioms checkChunk84_pass
def checkChunk85 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (10880+j)))
theorem checkChunk85_pass : checkChunk85 = true := by decide
#print axioms checkChunk85_pass
def checkChunk86 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (11008+j)))
theorem checkChunk86_pass : checkChunk86 = true := by decide
#print axioms checkChunk86_pass
def checkChunk87 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (11136+j)))
theorem checkChunk87_pass : checkChunk87 = true := by decide
#print axioms checkChunk87_pass
def checkChunk88 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (11264+j)))
theorem checkChunk88_pass : checkChunk88 = true := by decide
#print axioms checkChunk88_pass
def checkChunk89 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (11392+j)))
theorem checkChunk89_pass : checkChunk89 = true := by decide
#print axioms checkChunk89_pass
def checkChunk90 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (11520+j)))
theorem checkChunk90_pass : checkChunk90 = true := by decide
#print axioms checkChunk90_pass
def checkChunk91 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (11648+j)))
theorem checkChunk91_pass : checkChunk91 = true := by decide
#print axioms checkChunk91_pass
def checkChunk92 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (11776+j)))
theorem checkChunk92_pass : checkChunk92 = true := by decide
#print axioms checkChunk92_pass
def checkChunk93 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (11904+j)))
theorem checkChunk93_pass : checkChunk93 = true := by decide
#print axioms checkChunk93_pass
def checkChunk94 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (12032+j)))
theorem checkChunk94_pass : checkChunk94 = true := by decide
#print axioms checkChunk94_pass
def checkChunk95 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (12160+j)))
theorem checkChunk95_pass : checkChunk95 = true := by decide
#print axioms checkChunk95_pass
end ThomsonN10.Local.Certificates.AmbientKernel
