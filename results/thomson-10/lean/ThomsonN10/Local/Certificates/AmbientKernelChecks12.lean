/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk192 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (24576+j)))
theorem checkChunk192_pass : checkChunk192 = true := by decide
#print axioms checkChunk192_pass
def checkChunk193 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (24704+j)))
theorem checkChunk193_pass : checkChunk193 = true := by decide
#print axioms checkChunk193_pass
def checkChunk194 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (24832+j)))
theorem checkChunk194_pass : checkChunk194 = true := by decide
#print axioms checkChunk194_pass
def checkChunk195 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (24960+j)))
theorem checkChunk195_pass : checkChunk195 = true := by decide
#print axioms checkChunk195_pass
def checkChunk196 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (25088+j)))
theorem checkChunk196_pass : checkChunk196 = true := by decide
#print axioms checkChunk196_pass
def checkChunk197 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (25216+j)))
theorem checkChunk197_pass : checkChunk197 = true := by decide
#print axioms checkChunk197_pass
def checkChunk198 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (25344+j)))
theorem checkChunk198_pass : checkChunk198 = true := by decide
#print axioms checkChunk198_pass
def checkChunk199 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (25472+j)))
theorem checkChunk199_pass : checkChunk199 = true := by decide
#print axioms checkChunk199_pass
def checkChunk200 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (25600+j)))
theorem checkChunk200_pass : checkChunk200 = true := by decide
#print axioms checkChunk200_pass
def checkChunk201 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (25728+j)))
theorem checkChunk201_pass : checkChunk201 = true := by decide
#print axioms checkChunk201_pass
def checkChunk202 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (25856+j)))
theorem checkChunk202_pass : checkChunk202 = true := by decide
#print axioms checkChunk202_pass
def checkChunk203 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (25984+j)))
theorem checkChunk203_pass : checkChunk203 = true := by decide
#print axioms checkChunk203_pass
def checkChunk204 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (26112+j)))
theorem checkChunk204_pass : checkChunk204 = true := by decide
#print axioms checkChunk204_pass
def checkChunk205 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (26240+j)))
theorem checkChunk205_pass : checkChunk205 = true := by decide
#print axioms checkChunk205_pass
def checkChunk206 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (26368+j)))
theorem checkChunk206_pass : checkChunk206 = true := by decide
#print axioms checkChunk206_pass
def checkChunk207 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (26496+j)))
theorem checkChunk207_pass : checkChunk207 = true := by decide
#print axioms checkChunk207_pass
end ThomsonN10.Local.Certificates.AmbientKernel
