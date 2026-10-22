/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk256 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (32768+j)))
theorem checkChunk256_pass : checkChunk256 = true := by decide
#print axioms checkChunk256_pass
def checkChunk257 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (32896+j)))
theorem checkChunk257_pass : checkChunk257 = true := by decide
#print axioms checkChunk257_pass
def checkChunk258 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (33024+j)))
theorem checkChunk258_pass : checkChunk258 = true := by decide
#print axioms checkChunk258_pass
def checkChunk259 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (33152+j)))
theorem checkChunk259_pass : checkChunk259 = true := by decide
#print axioms checkChunk259_pass
def checkChunk260 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (33280+j)))
theorem checkChunk260_pass : checkChunk260 = true := by decide
#print axioms checkChunk260_pass
def checkChunk261 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (33408+j)))
theorem checkChunk261_pass : checkChunk261 = true := by decide
#print axioms checkChunk261_pass
def checkChunk262 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (33536+j)))
theorem checkChunk262_pass : checkChunk262 = true := by decide
#print axioms checkChunk262_pass
def checkChunk263 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (33664+j)))
theorem checkChunk263_pass : checkChunk263 = true := by decide
#print axioms checkChunk263_pass
def checkChunk264 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (33792+j)))
theorem checkChunk264_pass : checkChunk264 = true := by decide
#print axioms checkChunk264_pass
def checkChunk265 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (33920+j)))
theorem checkChunk265_pass : checkChunk265 = true := by decide
#print axioms checkChunk265_pass
def checkChunk266 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (34048+j)))
theorem checkChunk266_pass : checkChunk266 = true := by decide
#print axioms checkChunk266_pass
def checkChunk267 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (34176+j)))
theorem checkChunk267_pass : checkChunk267 = true := by decide
#print axioms checkChunk267_pass
def checkChunk268 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (34304+j)))
theorem checkChunk268_pass : checkChunk268 = true := by decide
#print axioms checkChunk268_pass
def checkChunk269 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (34432+j)))
theorem checkChunk269_pass : checkChunk269 = true := by decide
#print axioms checkChunk269_pass
def checkChunk270 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (34560+j)))
theorem checkChunk270_pass : checkChunk270 = true := by decide
#print axioms checkChunk270_pass
def checkChunk271 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (34688+j)))
theorem checkChunk271_pass : checkChunk271 = true := by decide
#print axioms checkChunk271_pass
end ThomsonN10.Local.Certificates.AmbientKernel
