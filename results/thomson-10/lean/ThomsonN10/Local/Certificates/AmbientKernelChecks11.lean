/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk176 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (22528+j)))
theorem checkChunk176_pass : checkChunk176 = true := by decide
#print axioms checkChunk176_pass
def checkChunk177 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (22656+j)))
theorem checkChunk177_pass : checkChunk177 = true := by decide
#print axioms checkChunk177_pass
def checkChunk178 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (22784+j)))
theorem checkChunk178_pass : checkChunk178 = true := by decide
#print axioms checkChunk178_pass
def checkChunk179 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (22912+j)))
theorem checkChunk179_pass : checkChunk179 = true := by decide
#print axioms checkChunk179_pass
def checkChunk180 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (23040+j)))
theorem checkChunk180_pass : checkChunk180 = true := by decide
#print axioms checkChunk180_pass
def checkChunk181 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (23168+j)))
theorem checkChunk181_pass : checkChunk181 = true := by decide
#print axioms checkChunk181_pass
def checkChunk182 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (23296+j)))
theorem checkChunk182_pass : checkChunk182 = true := by decide
#print axioms checkChunk182_pass
def checkChunk183 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (23424+j)))
theorem checkChunk183_pass : checkChunk183 = true := by decide
#print axioms checkChunk183_pass
def checkChunk184 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (23552+j)))
theorem checkChunk184_pass : checkChunk184 = true := by decide
#print axioms checkChunk184_pass
def checkChunk185 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (23680+j)))
theorem checkChunk185_pass : checkChunk185 = true := by decide
#print axioms checkChunk185_pass
def checkChunk186 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (23808+j)))
theorem checkChunk186_pass : checkChunk186 = true := by decide
#print axioms checkChunk186_pass
def checkChunk187 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (23936+j)))
theorem checkChunk187_pass : checkChunk187 = true := by decide
#print axioms checkChunk187_pass
def checkChunk188 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (24064+j)))
theorem checkChunk188_pass : checkChunk188 = true := by decide
#print axioms checkChunk188_pass
def checkChunk189 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (24192+j)))
theorem checkChunk189_pass : checkChunk189 = true := by decide
#print axioms checkChunk189_pass
def checkChunk190 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (24320+j)))
theorem checkChunk190_pass : checkChunk190 = true := by decide
#print axioms checkChunk190_pass
def checkChunk191 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (24448+j)))
theorem checkChunk191_pass : checkChunk191 = true := by decide
#print axioms checkChunk191_pass
end ThomsonN10.Local.Certificates.AmbientKernel
