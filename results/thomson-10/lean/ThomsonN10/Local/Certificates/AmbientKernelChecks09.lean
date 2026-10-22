/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk144 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (18432+j)))
theorem checkChunk144_pass : checkChunk144 = true := by decide
#print axioms checkChunk144_pass
def checkChunk145 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (18560+j)))
theorem checkChunk145_pass : checkChunk145 = true := by decide
#print axioms checkChunk145_pass
def checkChunk146 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (18688+j)))
theorem checkChunk146_pass : checkChunk146 = true := by decide
#print axioms checkChunk146_pass
def checkChunk147 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (18816+j)))
theorem checkChunk147_pass : checkChunk147 = true := by decide
#print axioms checkChunk147_pass
def checkChunk148 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (18944+j)))
theorem checkChunk148_pass : checkChunk148 = true := by decide
#print axioms checkChunk148_pass
def checkChunk149 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (19072+j)))
theorem checkChunk149_pass : checkChunk149 = true := by decide
#print axioms checkChunk149_pass
def checkChunk150 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (19200+j)))
theorem checkChunk150_pass : checkChunk150 = true := by decide
#print axioms checkChunk150_pass
def checkChunk151 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (19328+j)))
theorem checkChunk151_pass : checkChunk151 = true := by decide
#print axioms checkChunk151_pass
def checkChunk152 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (19456+j)))
theorem checkChunk152_pass : checkChunk152 = true := by decide
#print axioms checkChunk152_pass
def checkChunk153 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (19584+j)))
theorem checkChunk153_pass : checkChunk153 = true := by decide
#print axioms checkChunk153_pass
def checkChunk154 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (19712+j)))
theorem checkChunk154_pass : checkChunk154 = true := by decide
#print axioms checkChunk154_pass
def checkChunk155 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (19840+j)))
theorem checkChunk155_pass : checkChunk155 = true := by decide
#print axioms checkChunk155_pass
def checkChunk156 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (19968+j)))
theorem checkChunk156_pass : checkChunk156 = true := by decide
#print axioms checkChunk156_pass
def checkChunk157 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (20096+j)))
theorem checkChunk157_pass : checkChunk157 = true := by decide
#print axioms checkChunk157_pass
def checkChunk158 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (20224+j)))
theorem checkChunk158_pass : checkChunk158 = true := by decide
#print axioms checkChunk158_pass
def checkChunk159 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (20352+j)))
theorem checkChunk159_pass : checkChunk159 = true := by decide
#print axioms checkChunk159_pass
end ThomsonN10.Local.Certificates.AmbientKernel
