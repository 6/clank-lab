/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk240 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (30720+j)))
theorem checkChunk240_pass : checkChunk240 = true := by decide
#print axioms checkChunk240_pass
def checkChunk241 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (30848+j)))
theorem checkChunk241_pass : checkChunk241 = true := by decide
#print axioms checkChunk241_pass
def checkChunk242 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (30976+j)))
theorem checkChunk242_pass : checkChunk242 = true := by decide
#print axioms checkChunk242_pass
def checkChunk243 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (31104+j)))
theorem checkChunk243_pass : checkChunk243 = true := by decide
#print axioms checkChunk243_pass
def checkChunk244 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (31232+j)))
theorem checkChunk244_pass : checkChunk244 = true := by decide
#print axioms checkChunk244_pass
def checkChunk245 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (31360+j)))
theorem checkChunk245_pass : checkChunk245 = true := by decide
#print axioms checkChunk245_pass
def checkChunk246 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (31488+j)))
theorem checkChunk246_pass : checkChunk246 = true := by decide
#print axioms checkChunk246_pass
def checkChunk247 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (31616+j)))
theorem checkChunk247_pass : checkChunk247 = true := by decide
#print axioms checkChunk247_pass
def checkChunk248 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (31744+j)))
theorem checkChunk248_pass : checkChunk248 = true := by decide
#print axioms checkChunk248_pass
def checkChunk249 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (31872+j)))
theorem checkChunk249_pass : checkChunk249 = true := by decide
#print axioms checkChunk249_pass
def checkChunk250 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (32000+j)))
theorem checkChunk250_pass : checkChunk250 = true := by decide
#print axioms checkChunk250_pass
def checkChunk251 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (32128+j)))
theorem checkChunk251_pass : checkChunk251 = true := by decide
#print axioms checkChunk251_pass
def checkChunk252 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (32256+j)))
theorem checkChunk252_pass : checkChunk252 = true := by decide
#print axioms checkChunk252_pass
def checkChunk253 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (32384+j)))
theorem checkChunk253_pass : checkChunk253 = true := by decide
#print axioms checkChunk253_pass
def checkChunk254 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (32512+j)))
theorem checkChunk254_pass : checkChunk254 = true := by decide
#print axioms checkChunk254_pass
def checkChunk255 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (32640+j)))
theorem checkChunk255_pass : checkChunk255 = true := by decide
#print axioms checkChunk255_pass
end ThomsonN10.Local.Certificates.AmbientKernel
