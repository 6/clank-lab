/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk208 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (26624+j)))
theorem checkChunk208_pass : checkChunk208 = true := by decide
#print axioms checkChunk208_pass
def checkChunk209 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (26752+j)))
theorem checkChunk209_pass : checkChunk209 = true := by decide
#print axioms checkChunk209_pass
def checkChunk210 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (26880+j)))
theorem checkChunk210_pass : checkChunk210 = true := by decide
#print axioms checkChunk210_pass
def checkChunk211 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (27008+j)))
theorem checkChunk211_pass : checkChunk211 = true := by decide
#print axioms checkChunk211_pass
def checkChunk212 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (27136+j)))
theorem checkChunk212_pass : checkChunk212 = true := by decide
#print axioms checkChunk212_pass
def checkChunk213 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (27264+j)))
theorem checkChunk213_pass : checkChunk213 = true := by decide
#print axioms checkChunk213_pass
def checkChunk214 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (27392+j)))
theorem checkChunk214_pass : checkChunk214 = true := by decide
#print axioms checkChunk214_pass
def checkChunk215 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (27520+j)))
theorem checkChunk215_pass : checkChunk215 = true := by decide
#print axioms checkChunk215_pass
def checkChunk216 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (27648+j)))
theorem checkChunk216_pass : checkChunk216 = true := by decide
#print axioms checkChunk216_pass
def checkChunk217 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (27776+j)))
theorem checkChunk217_pass : checkChunk217 = true := by decide
#print axioms checkChunk217_pass
def checkChunk218 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (27904+j)))
theorem checkChunk218_pass : checkChunk218 = true := by decide
#print axioms checkChunk218_pass
def checkChunk219 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (28032+j)))
theorem checkChunk219_pass : checkChunk219 = true := by decide
#print axioms checkChunk219_pass
def checkChunk220 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (28160+j)))
theorem checkChunk220_pass : checkChunk220 = true := by decide
#print axioms checkChunk220_pass
def checkChunk221 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (28288+j)))
theorem checkChunk221_pass : checkChunk221 = true := by decide
#print axioms checkChunk221_pass
def checkChunk222 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (28416+j)))
theorem checkChunk222_pass : checkChunk222 = true := by decide
#print axioms checkChunk222_pass
def checkChunk223 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (28544+j)))
theorem checkChunk223_pass : checkChunk223 = true := by decide
#print axioms checkChunk223_pass
end ThomsonN10.Local.Certificates.AmbientKernel
