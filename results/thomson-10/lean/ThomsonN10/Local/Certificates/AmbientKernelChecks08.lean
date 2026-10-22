/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk128 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (16384+j)))
theorem checkChunk128_pass : checkChunk128 = true := by decide
#print axioms checkChunk128_pass
def checkChunk129 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (16512+j)))
theorem checkChunk129_pass : checkChunk129 = true := by decide
#print axioms checkChunk129_pass
def checkChunk130 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (16640+j)))
theorem checkChunk130_pass : checkChunk130 = true := by decide
#print axioms checkChunk130_pass
def checkChunk131 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (16768+j)))
theorem checkChunk131_pass : checkChunk131 = true := by decide
#print axioms checkChunk131_pass
def checkChunk132 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (16896+j)))
theorem checkChunk132_pass : checkChunk132 = true := by decide
#print axioms checkChunk132_pass
def checkChunk133 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (17024+j)))
theorem checkChunk133_pass : checkChunk133 = true := by decide
#print axioms checkChunk133_pass
def checkChunk134 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (17152+j)))
theorem checkChunk134_pass : checkChunk134 = true := by decide
#print axioms checkChunk134_pass
def checkChunk135 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (17280+j)))
theorem checkChunk135_pass : checkChunk135 = true := by decide
#print axioms checkChunk135_pass
def checkChunk136 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (17408+j)))
theorem checkChunk136_pass : checkChunk136 = true := by decide
#print axioms checkChunk136_pass
def checkChunk137 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (17536+j)))
theorem checkChunk137_pass : checkChunk137 = true := by decide
#print axioms checkChunk137_pass
def checkChunk138 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (17664+j)))
theorem checkChunk138_pass : checkChunk138 = true := by decide
#print axioms checkChunk138_pass
def checkChunk139 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (17792+j)))
theorem checkChunk139_pass : checkChunk139 = true := by decide
#print axioms checkChunk139_pass
def checkChunk140 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (17920+j)))
theorem checkChunk140_pass : checkChunk140 = true := by decide
#print axioms checkChunk140_pass
def checkChunk141 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (18048+j)))
theorem checkChunk141_pass : checkChunk141 = true := by decide
#print axioms checkChunk141_pass
def checkChunk142 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (18176+j)))
theorem checkChunk142_pass : checkChunk142 = true := by decide
#print axioms checkChunk142_pass
def checkChunk143 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (18304+j)))
theorem checkChunk143_pass : checkChunk143 = true := by decide
#print axioms checkChunk143_pass
end ThomsonN10.Local.Certificates.AmbientKernel
