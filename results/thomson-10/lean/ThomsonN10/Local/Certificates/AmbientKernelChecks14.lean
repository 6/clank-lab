/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk224 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (28672+j)))
theorem checkChunk224_pass : checkChunk224 = true := by decide
#print axioms checkChunk224_pass
def checkChunk225 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (28800+j)))
theorem checkChunk225_pass : checkChunk225 = true := by decide
#print axioms checkChunk225_pass
def checkChunk226 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (28928+j)))
theorem checkChunk226_pass : checkChunk226 = true := by decide
#print axioms checkChunk226_pass
def checkChunk227 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (29056+j)))
theorem checkChunk227_pass : checkChunk227 = true := by decide
#print axioms checkChunk227_pass
def checkChunk228 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (29184+j)))
theorem checkChunk228_pass : checkChunk228 = true := by decide
#print axioms checkChunk228_pass
def checkChunk229 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (29312+j)))
theorem checkChunk229_pass : checkChunk229 = true := by decide
#print axioms checkChunk229_pass
def checkChunk230 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (29440+j)))
theorem checkChunk230_pass : checkChunk230 = true := by decide
#print axioms checkChunk230_pass
def checkChunk231 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (29568+j)))
theorem checkChunk231_pass : checkChunk231 = true := by decide
#print axioms checkChunk231_pass
def checkChunk232 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (29696+j)))
theorem checkChunk232_pass : checkChunk232 = true := by decide
#print axioms checkChunk232_pass
def checkChunk233 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (29824+j)))
theorem checkChunk233_pass : checkChunk233 = true := by decide
#print axioms checkChunk233_pass
def checkChunk234 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (29952+j)))
theorem checkChunk234_pass : checkChunk234 = true := by decide
#print axioms checkChunk234_pass
def checkChunk235 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (30080+j)))
theorem checkChunk235_pass : checkChunk235 = true := by decide
#print axioms checkChunk235_pass
def checkChunk236 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (30208+j)))
theorem checkChunk236_pass : checkChunk236 = true := by decide
#print axioms checkChunk236_pass
def checkChunk237 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (30336+j)))
theorem checkChunk237_pass : checkChunk237 = true := by decide
#print axioms checkChunk237_pass
def checkChunk238 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (30464+j)))
theorem checkChunk238_pass : checkChunk238 = true := by decide
#print axioms checkChunk238_pass
def checkChunk239 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (30592+j)))
theorem checkChunk239_pass : checkChunk239 = true := by decide
#print axioms checkChunk239_pass
end ThomsonN10.Local.Certificates.AmbientKernel
