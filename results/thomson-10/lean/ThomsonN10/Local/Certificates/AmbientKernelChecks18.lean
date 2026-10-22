/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk288 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (36864+j)))
theorem checkChunk288_pass : checkChunk288 = true := by decide
#print axioms checkChunk288_pass
def checkChunk289 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (36992+j)))
theorem checkChunk289_pass : checkChunk289 = true := by decide
#print axioms checkChunk289_pass
def checkChunk290 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (37120+j)))
theorem checkChunk290_pass : checkChunk290 = true := by decide
#print axioms checkChunk290_pass
def checkChunk291 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (37248+j)))
theorem checkChunk291_pass : checkChunk291 = true := by decide
#print axioms checkChunk291_pass
def checkChunk292 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (37376+j)))
theorem checkChunk292_pass : checkChunk292 = true := by decide
#print axioms checkChunk292_pass
def checkChunk293 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (37504+j)))
theorem checkChunk293_pass : checkChunk293 = true := by decide
#print axioms checkChunk293_pass
def checkChunk294 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (37632+j)))
theorem checkChunk294_pass : checkChunk294 = true := by decide
#print axioms checkChunk294_pass
def checkChunk295 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (37760+j)))
theorem checkChunk295_pass : checkChunk295 = true := by decide
#print axioms checkChunk295_pass
def checkChunk296 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (37888+j)))
theorem checkChunk296_pass : checkChunk296 = true := by decide
#print axioms checkChunk296_pass
def checkChunk297 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (38016+j)))
theorem checkChunk297_pass : checkChunk297 = true := by decide
#print axioms checkChunk297_pass
def checkChunk298 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (38144+j)))
theorem checkChunk298_pass : checkChunk298 = true := by decide
#print axioms checkChunk298_pass
def checkChunk299 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (38272+j)))
theorem checkChunk299_pass : checkChunk299 = true := by decide
#print axioms checkChunk299_pass
def checkChunk300 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (38400+j)))
theorem checkChunk300_pass : checkChunk300 = true := by decide
#print axioms checkChunk300_pass
def checkChunk301 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (38528+j)))
theorem checkChunk301_pass : checkChunk301 = true := by decide
#print axioms checkChunk301_pass
def checkChunk302 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (38656+j)))
theorem checkChunk302_pass : checkChunk302 = true := by decide
#print axioms checkChunk302_pass
def checkChunk303 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (38784+j)))
theorem checkChunk303_pass : checkChunk303 = true := by decide
#print axioms checkChunk303_pass
end ThomsonN10.Local.Certificates.AmbientKernel
