import Lake
open System Lake DSL

package ThomsonN10

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- Expand the large exact certificate before Lean reads its imports. -/
target ambientData pkg : FilePath := do
  let compressed := pkg.dir / "ThomsonN10/Local/Certificates/AmbientKernelData.lean.gz"
  let destination := pkg.dir / "ThomsonN10/Local/Certificates/AmbientKernelData.lean"
  let dependency ← inputBinFile compressed
  dependency.mapM fun source => do
    addTrace BuildTrace.nil
    -- Lean imports this source path, not the artifact's path in Lake's cache.
    -- Restore it even when the compressed input already has a cached output.
    let artifact ← buildArtifactUnlessUpToDate destination (do
      let result ← IO.Process.output {cmd := "gzip", args := #["-dc", source.toString]}
      unless result.exitCode == 0 do error "certificate decompression failed"
      IO.FS.writeFile destination result.stdout) (restore := true)
    return artifact.path

lean_lib ThomsonN10 where
  extraDepTargets := #[`ambientData]

lean_lib Challenge

lean_lib Solution

lean_lib Publication where
  extraDepTargets := #[`ambientData]

/-- Generate the source before Lake discovers the libraries' imports. -/
@[default_target]
target proof : Unit := do
  discard (← ambientData.fetch).await
  return Job.mixArray #[← ThomsonN10.fetch, ← Solution.fetch, ← Publication.fetch]
