/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk352 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (45056+j)))
theorem checkChunk352_pass : checkChunk352 = true := by decide
#print axioms checkChunk352_pass
def checkChunk353 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (45184+j)))
theorem checkChunk353_pass : checkChunk353 = true := by decide
#print axioms checkChunk353_pass
def checkChunk354 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (45312+j)))
theorem checkChunk354_pass : checkChunk354 = true := by decide
#print axioms checkChunk354_pass
def checkChunk355 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (45440+j)))
theorem checkChunk355_pass : checkChunk355 = true := by decide
#print axioms checkChunk355_pass
def checkChunk356 : Bool := (List.range 24).all
  (fun j => decide (Node.Check scale inputs nodes (45568+j)))
theorem checkChunk356_pass : checkChunk356 = true := by decide
#print axioms checkChunk356_pass
end ThomsonN10.Local.Certificates.AmbientKernel
