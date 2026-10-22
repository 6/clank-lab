/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk272 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (34816+j)))
theorem checkChunk272_pass : checkChunk272 = true := by decide
#print axioms checkChunk272_pass
def checkChunk273 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (34944+j)))
theorem checkChunk273_pass : checkChunk273 = true := by decide
#print axioms checkChunk273_pass
def checkChunk274 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (35072+j)))
theorem checkChunk274_pass : checkChunk274 = true := by decide
#print axioms checkChunk274_pass
def checkChunk275 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (35200+j)))
theorem checkChunk275_pass : checkChunk275 = true := by decide
#print axioms checkChunk275_pass
def checkChunk276 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (35328+j)))
theorem checkChunk276_pass : checkChunk276 = true := by decide
#print axioms checkChunk276_pass
def checkChunk277 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (35456+j)))
theorem checkChunk277_pass : checkChunk277 = true := by decide
#print axioms checkChunk277_pass
def checkChunk278 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (35584+j)))
theorem checkChunk278_pass : checkChunk278 = true := by decide
#print axioms checkChunk278_pass
def checkChunk279 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (35712+j)))
theorem checkChunk279_pass : checkChunk279 = true := by decide
#print axioms checkChunk279_pass
def checkChunk280 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (35840+j)))
theorem checkChunk280_pass : checkChunk280 = true := by decide
#print axioms checkChunk280_pass
def checkChunk281 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (35968+j)))
theorem checkChunk281_pass : checkChunk281 = true := by decide
#print axioms checkChunk281_pass
def checkChunk282 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (36096+j)))
theorem checkChunk282_pass : checkChunk282 = true := by decide
#print axioms checkChunk282_pass
def checkChunk283 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (36224+j)))
theorem checkChunk283_pass : checkChunk283 = true := by decide
#print axioms checkChunk283_pass
def checkChunk284 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (36352+j)))
theorem checkChunk284_pass : checkChunk284 = true := by decide
#print axioms checkChunk284_pass
def checkChunk285 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (36480+j)))
theorem checkChunk285_pass : checkChunk285 = true := by decide
#print axioms checkChunk285_pass
def checkChunk286 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (36608+j)))
theorem checkChunk286_pass : checkChunk286 = true := by decide
#print axioms checkChunk286_pass
def checkChunk287 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (36736+j)))
theorem checkChunk287_pass : checkChunk287 = true := by decide
#print axioms checkChunk287_pass
end ThomsonN10.Local.Certificates.AmbientKernel
