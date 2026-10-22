/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk160 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (20480+j)))
theorem checkChunk160_pass : checkChunk160 = true := by decide
#print axioms checkChunk160_pass
def checkChunk161 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (20608+j)))
theorem checkChunk161_pass : checkChunk161 = true := by decide
#print axioms checkChunk161_pass
def checkChunk162 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (20736+j)))
theorem checkChunk162_pass : checkChunk162 = true := by decide
#print axioms checkChunk162_pass
def checkChunk163 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (20864+j)))
theorem checkChunk163_pass : checkChunk163 = true := by decide
#print axioms checkChunk163_pass
def checkChunk164 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (20992+j)))
theorem checkChunk164_pass : checkChunk164 = true := by decide
#print axioms checkChunk164_pass
def checkChunk165 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (21120+j)))
theorem checkChunk165_pass : checkChunk165 = true := by decide
#print axioms checkChunk165_pass
def checkChunk166 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (21248+j)))
theorem checkChunk166_pass : checkChunk166 = true := by decide
#print axioms checkChunk166_pass
def checkChunk167 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (21376+j)))
theorem checkChunk167_pass : checkChunk167 = true := by decide
#print axioms checkChunk167_pass
def checkChunk168 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (21504+j)))
theorem checkChunk168_pass : checkChunk168 = true := by decide
#print axioms checkChunk168_pass
def checkChunk169 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (21632+j)))
theorem checkChunk169_pass : checkChunk169 = true := by decide
#print axioms checkChunk169_pass
def checkChunk170 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (21760+j)))
theorem checkChunk170_pass : checkChunk170 = true := by decide
#print axioms checkChunk170_pass
def checkChunk171 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (21888+j)))
theorem checkChunk171_pass : checkChunk171 = true := by decide
#print axioms checkChunk171_pass
def checkChunk172 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (22016+j)))
theorem checkChunk172_pass : checkChunk172 = true := by decide
#print axioms checkChunk172_pass
def checkChunk173 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (22144+j)))
theorem checkChunk173_pass : checkChunk173 = true := by decide
#print axioms checkChunk173_pass
def checkChunk174 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (22272+j)))
theorem checkChunk174_pass : checkChunk174 = true := by decide
#print axioms checkChunk174_pass
def checkChunk175 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (22400+j)))
theorem checkChunk175_pass : checkChunk175 = true := by decide
#print axioms checkChunk175_pass
end ThomsonN10.Local.Certificates.AmbientKernel
