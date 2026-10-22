/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk16 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (2048+j)))
theorem checkChunk16_pass : checkChunk16 = true := by decide
#print axioms checkChunk16_pass
def checkChunk17 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (2176+j)))
theorem checkChunk17_pass : checkChunk17 = true := by decide
#print axioms checkChunk17_pass
def checkChunk18 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (2304+j)))
theorem checkChunk18_pass : checkChunk18 = true := by decide
#print axioms checkChunk18_pass
def checkChunk19 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (2432+j)))
theorem checkChunk19_pass : checkChunk19 = true := by decide
#print axioms checkChunk19_pass
def checkChunk20 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (2560+j)))
theorem checkChunk20_pass : checkChunk20 = true := by decide
#print axioms checkChunk20_pass
def checkChunk21 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (2688+j)))
theorem checkChunk21_pass : checkChunk21 = true := by decide
#print axioms checkChunk21_pass
def checkChunk22 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (2816+j)))
theorem checkChunk22_pass : checkChunk22 = true := by decide
#print axioms checkChunk22_pass
def checkChunk23 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (2944+j)))
theorem checkChunk23_pass : checkChunk23 = true := by decide
#print axioms checkChunk23_pass
def checkChunk24 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (3072+j)))
theorem checkChunk24_pass : checkChunk24 = true := by decide
#print axioms checkChunk24_pass
def checkChunk25 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (3200+j)))
theorem checkChunk25_pass : checkChunk25 = true := by decide
#print axioms checkChunk25_pass
def checkChunk26 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (3328+j)))
theorem checkChunk26_pass : checkChunk26 = true := by decide
#print axioms checkChunk26_pass
def checkChunk27 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (3456+j)))
theorem checkChunk27_pass : checkChunk27 = true := by decide
#print axioms checkChunk27_pass
def checkChunk28 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (3584+j)))
theorem checkChunk28_pass : checkChunk28 = true := by decide
#print axioms checkChunk28_pass
def checkChunk29 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (3712+j)))
theorem checkChunk29_pass : checkChunk29 = true := by decide
#print axioms checkChunk29_pass
def checkChunk30 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (3840+j)))
theorem checkChunk30_pass : checkChunk30 = true := by decide
#print axioms checkChunk30_pass
def checkChunk31 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (3968+j)))
theorem checkChunk31_pass : checkChunk31 = true := by decide
#print axioms checkChunk31_pass
end ThomsonN10.Local.Certificates.AmbientKernel
