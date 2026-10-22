/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def checkChunk64 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (8192+j)))
theorem checkChunk64_pass : checkChunk64 = true := by decide
#print axioms checkChunk64_pass
def checkChunk65 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (8320+j)))
theorem checkChunk65_pass : checkChunk65 = true := by decide
#print axioms checkChunk65_pass
def checkChunk66 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (8448+j)))
theorem checkChunk66_pass : checkChunk66 = true := by decide
#print axioms checkChunk66_pass
def checkChunk67 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (8576+j)))
theorem checkChunk67_pass : checkChunk67 = true := by decide
#print axioms checkChunk67_pass
def checkChunk68 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (8704+j)))
theorem checkChunk68_pass : checkChunk68 = true := by decide
#print axioms checkChunk68_pass
def checkChunk69 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (8832+j)))
theorem checkChunk69_pass : checkChunk69 = true := by decide
#print axioms checkChunk69_pass
def checkChunk70 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (8960+j)))
theorem checkChunk70_pass : checkChunk70 = true := by decide
#print axioms checkChunk70_pass
def checkChunk71 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (9088+j)))
theorem checkChunk71_pass : checkChunk71 = true := by decide
#print axioms checkChunk71_pass
def checkChunk72 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (9216+j)))
theorem checkChunk72_pass : checkChunk72 = true := by decide
#print axioms checkChunk72_pass
def checkChunk73 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (9344+j)))
theorem checkChunk73_pass : checkChunk73 = true := by decide
#print axioms checkChunk73_pass
def checkChunk74 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (9472+j)))
theorem checkChunk74_pass : checkChunk74 = true := by decide
#print axioms checkChunk74_pass
def checkChunk75 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (9600+j)))
theorem checkChunk75_pass : checkChunk75 = true := by decide
#print axioms checkChunk75_pass
def checkChunk76 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (9728+j)))
theorem checkChunk76_pass : checkChunk76 = true := by decide
#print axioms checkChunk76_pass
def checkChunk77 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (9856+j)))
theorem checkChunk77_pass : checkChunk77 = true := by decide
#print axioms checkChunk77_pass
def checkChunk78 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (9984+j)))
theorem checkChunk78_pass : checkChunk78 = true := by decide
#print axioms checkChunk78_pass
def checkChunk79 : Bool := (List.range 128).all
  (fun j => decide (Node.Check scale inputs nodes (10112+j)))
theorem checkChunk79_pass : checkChunk79 = true := by decide
#print axioms checkChunk79_pass
end ThomsonN10.Local.Certificates.AmbientKernel
