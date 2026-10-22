/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk32 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (4096+j)))
theorem checkChunk32_pass : checkChunk32 = true := by decide
#print axioms checkChunk32_pass
def checkChunk33 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (4224+j)))
theorem checkChunk33_pass : checkChunk33 = true := by decide
#print axioms checkChunk33_pass
def checkChunk34 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (4352+j)))
theorem checkChunk34_pass : checkChunk34 = true := by decide
#print axioms checkChunk34_pass
def checkChunk35 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (4480+j)))
theorem checkChunk35_pass : checkChunk35 = true := by decide
#print axioms checkChunk35_pass
def checkChunk36 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (4608+j)))
theorem checkChunk36_pass : checkChunk36 = true := by decide
#print axioms checkChunk36_pass
def checkChunk37 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (4736+j)))
theorem checkChunk37_pass : checkChunk37 = true := by decide
#print axioms checkChunk37_pass
def checkChunk38 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (4864+j)))
theorem checkChunk38_pass : checkChunk38 = true := by decide
#print axioms checkChunk38_pass
def checkChunk39 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (4992+j)))
theorem checkChunk39_pass : checkChunk39 = true := by decide
#print axioms checkChunk39_pass
def checkChunk40 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (5120+j)))
theorem checkChunk40_pass : checkChunk40 = true := by decide
#print axioms checkChunk40_pass
def checkChunk41 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (5248+j)))
theorem checkChunk41_pass : checkChunk41 = true := by decide
#print axioms checkChunk41_pass
def checkChunk42 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (5376+j)))
theorem checkChunk42_pass : checkChunk42 = true := by decide
#print axioms checkChunk42_pass
def checkChunk43 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (5504+j)))
theorem checkChunk43_pass : checkChunk43 = true := by decide
#print axioms checkChunk43_pass
def checkChunk44 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (5632+j)))
theorem checkChunk44_pass : checkChunk44 = true := by decide
#print axioms checkChunk44_pass
def checkChunk45 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (5760+j)))
theorem checkChunk45_pass : checkChunk45 = true := by decide
#print axioms checkChunk45_pass
def checkChunk46 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (5888+j)))
theorem checkChunk46_pass : checkChunk46 = true := by decide
#print axioms checkChunk46_pass
def checkChunk47 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (6016+j)))
theorem checkChunk47_pass : checkChunk47 = true := by decide
#print axioms checkChunk47_pass
end ThomsonN10.Local.Certificates.AmbientKernel
