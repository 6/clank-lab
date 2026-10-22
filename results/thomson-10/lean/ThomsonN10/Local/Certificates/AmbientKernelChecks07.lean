/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk112 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (14336+j)))
theorem checkChunk112_pass : checkChunk112 = true := by decide
#print axioms checkChunk112_pass
def checkChunk113 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (14464+j)))
theorem checkChunk113_pass : checkChunk113 = true := by decide
#print axioms checkChunk113_pass
def checkChunk114 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (14592+j)))
theorem checkChunk114_pass : checkChunk114 = true := by decide
#print axioms checkChunk114_pass
def checkChunk115 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (14720+j)))
theorem checkChunk115_pass : checkChunk115 = true := by decide
#print axioms checkChunk115_pass
def checkChunk116 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (14848+j)))
theorem checkChunk116_pass : checkChunk116 = true := by decide
#print axioms checkChunk116_pass
def checkChunk117 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (14976+j)))
theorem checkChunk117_pass : checkChunk117 = true := by decide
#print axioms checkChunk117_pass
def checkChunk118 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (15104+j)))
theorem checkChunk118_pass : checkChunk118 = true := by decide
#print axioms checkChunk118_pass
def checkChunk119 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (15232+j)))
theorem checkChunk119_pass : checkChunk119 = true := by decide
#print axioms checkChunk119_pass
def checkChunk120 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (15360+j)))
theorem checkChunk120_pass : checkChunk120 = true := by decide
#print axioms checkChunk120_pass
def checkChunk121 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (15488+j)))
theorem checkChunk121_pass : checkChunk121 = true := by decide
#print axioms checkChunk121_pass
def checkChunk122 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (15616+j)))
theorem checkChunk122_pass : checkChunk122 = true := by decide
#print axioms checkChunk122_pass
def checkChunk123 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (15744+j)))
theorem checkChunk123_pass : checkChunk123 = true := by decide
#print axioms checkChunk123_pass
def checkChunk124 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (15872+j)))
theorem checkChunk124_pass : checkChunk124 = true := by decide
#print axioms checkChunk124_pass
def checkChunk125 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (16000+j)))
theorem checkChunk125_pass : checkChunk125 = true := by decide
#print axioms checkChunk125_pass
def checkChunk126 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (16128+j)))
theorem checkChunk126_pass : checkChunk126 = true := by decide
#print axioms checkChunk126_pass
def checkChunk127 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (16256+j)))
theorem checkChunk127_pass : checkChunk127 = true := by decide
#print axioms checkChunk127_pass
end ThomsonN10.Local.Certificates.AmbientKernel
