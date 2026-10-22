/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk304 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (38912+j)))
theorem checkChunk304_pass : checkChunk304 = true := by decide
#print axioms checkChunk304_pass
def checkChunk305 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (39040+j)))
theorem checkChunk305_pass : checkChunk305 = true := by decide
#print axioms checkChunk305_pass
def checkChunk306 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (39168+j)))
theorem checkChunk306_pass : checkChunk306 = true := by decide
#print axioms checkChunk306_pass
def checkChunk307 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (39296+j)))
theorem checkChunk307_pass : checkChunk307 = true := by decide
#print axioms checkChunk307_pass
def checkChunk308 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (39424+j)))
theorem checkChunk308_pass : checkChunk308 = true := by decide
#print axioms checkChunk308_pass
def checkChunk309 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (39552+j)))
theorem checkChunk309_pass : checkChunk309 = true := by decide
#print axioms checkChunk309_pass
def checkChunk310 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (39680+j)))
theorem checkChunk310_pass : checkChunk310 = true := by decide
#print axioms checkChunk310_pass
def checkChunk311 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (39808+j)))
theorem checkChunk311_pass : checkChunk311 = true := by decide
#print axioms checkChunk311_pass
def checkChunk312 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (39936+j)))
theorem checkChunk312_pass : checkChunk312 = true := by decide
#print axioms checkChunk312_pass
def checkChunk313 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (40064+j)))
theorem checkChunk313_pass : checkChunk313 = true := by decide
#print axioms checkChunk313_pass
def checkChunk314 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (40192+j)))
theorem checkChunk314_pass : checkChunk314 = true := by decide
#print axioms checkChunk314_pass
def checkChunk315 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (40320+j)))
theorem checkChunk315_pass : checkChunk315 = true := by decide
#print axioms checkChunk315_pass
def checkChunk316 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (40448+j)))
theorem checkChunk316_pass : checkChunk316 = true := by decide
#print axioms checkChunk316_pass
def checkChunk317 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (40576+j)))
theorem checkChunk317_pass : checkChunk317 = true := by decide
#print axioms checkChunk317_pass
def checkChunk318 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (40704+j)))
theorem checkChunk318_pass : checkChunk318 = true := by decide
#print axioms checkChunk318_pass
def checkChunk319 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (40832+j)))
theorem checkChunk319_pass : checkChunk319 = true := by decide
#print axioms checkChunk319_pass
end ThomsonN10.Local.Certificates.AmbientKernel
