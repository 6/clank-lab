/- Adapted from proof/ambient_circuit/export_lean_full.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelChecks00
import ThomsonN10.Local.Certificates.AmbientKernelChecks01
import ThomsonN10.Local.Certificates.AmbientKernelChecks02
import ThomsonN10.Local.Certificates.AmbientKernelChecks03
import ThomsonN10.Local.Certificates.AmbientKernelChecks04
import ThomsonN10.Local.Certificates.AmbientKernelChecks05
import ThomsonN10.Local.Certificates.AmbientKernelChecks06
import ThomsonN10.Local.Certificates.AmbientKernelChecks07
import ThomsonN10.Local.Certificates.AmbientKernelChecks08
import ThomsonN10.Local.Certificates.AmbientKernelChecks09
import ThomsonN10.Local.Certificates.AmbientKernelChecks10
import ThomsonN10.Local.Certificates.AmbientKernelChecks11
import ThomsonN10.Local.Certificates.AmbientKernelChecks12
import ThomsonN10.Local.Certificates.AmbientKernelChecks13
import ThomsonN10.Local.Certificates.AmbientKernelChecks14
import ThomsonN10.Local.Certificates.AmbientKernelChecks15
import ThomsonN10.Local.Certificates.AmbientKernelChecks16
import ThomsonN10.Local.Certificates.AmbientKernelChecks17
import ThomsonN10.Local.Certificates.AmbientKernelChecks18
import ThomsonN10.Local.Certificates.AmbientKernelChecks19
import ThomsonN10.Local.Certificates.AmbientKernelChecks20
import ThomsonN10.Local.Certificates.AmbientKernelChecks21
import ThomsonN10.Local.Certificates.AmbientKernelChecks22
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
theorem node_checks (i : ℕ) (hi : i < 45592) :
    Node.Check scale inputs nodes i := by
  by_cases h0 : i < 22784
  ·
    by_cases h1 : i < 11392
    ·
      by_cases h2 : i < 5632
      ·
        by_cases h3 : i < 2816
        ·
          by_cases h4 : i < 1408
          ·
            by_cases h5 : i < 640
            ·
              by_cases h6 : i < 256
              ·
                by_cases h7 : i < 128
                ·
                  have h := List.all_eq_true.mp checkChunk0_pass (i-0)
                    (List.mem_range.mpr (by omega))
                  have heq : 0+(i-0) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (0+(i-0)))
                ·
                  have h := List.all_eq_true.mp checkChunk1_pass (i-128)
                    (List.mem_range.mpr (by omega))
                  have heq : 128+(i-128) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (128+(i-128)))
              ·
                by_cases h7 : i < 384
                ·
                  have h := List.all_eq_true.mp checkChunk2_pass (i-256)
                    (List.mem_range.mpr (by omega))
                  have heq : 256+(i-256) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (256+(i-256)))
                ·
                  by_cases h8 : i < 512
                  ·
                    have h := List.all_eq_true.mp checkChunk3_pass (i-384)
                      (List.mem_range.mpr (by omega))
                    have heq : 384+(i-384) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (384+(i-384)))
                  ·
                    have h := List.all_eq_true.mp checkChunk4_pass (i-512)
                      (List.mem_range.mpr (by omega))
                    have heq : 512+(i-512) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (512+(i-512)))
            ·
              by_cases h6 : i < 1024
              ·
                by_cases h7 : i < 768
                ·
                  have h := List.all_eq_true.mp checkChunk5_pass (i-640)
                    (List.mem_range.mpr (by omega))
                  have heq : 640+(i-640) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (640+(i-640)))
                ·
                  by_cases h8 : i < 896
                  ·
                    have h := List.all_eq_true.mp checkChunk6_pass (i-768)
                      (List.mem_range.mpr (by omega))
                    have heq : 768+(i-768) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (768+(i-768)))
                  ·
                    have h := List.all_eq_true.mp checkChunk7_pass (i-896)
                      (List.mem_range.mpr (by omega))
                    have heq : 896+(i-896) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (896+(i-896)))
              ·
                by_cases h7 : i < 1152
                ·
                  have h := List.all_eq_true.mp checkChunk8_pass (i-1024)
                    (List.mem_range.mpr (by omega))
                  have heq : 1024+(i-1024) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (1024+(i-1024)))
                ·
                  by_cases h8 : i < 1280
                  ·
                    have h := List.all_eq_true.mp checkChunk9_pass (i-1152)
                      (List.mem_range.mpr (by omega))
                    have heq : 1152+(i-1152) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (1152+(i-1152)))
                  ·
                    have h := List.all_eq_true.mp checkChunk10_pass (i-1280)
                      (List.mem_range.mpr (by omega))
                    have heq : 1280+(i-1280) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (1280+(i-1280)))
          ·
            by_cases h5 : i < 2048
            ·
              by_cases h6 : i < 1664
              ·
                by_cases h7 : i < 1536
                ·
                  have h := List.all_eq_true.mp checkChunk11_pass (i-1408)
                    (List.mem_range.mpr (by omega))
                  have heq : 1408+(i-1408) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (1408+(i-1408)))
                ·
                  have h := List.all_eq_true.mp checkChunk12_pass (i-1536)
                    (List.mem_range.mpr (by omega))
                  have heq : 1536+(i-1536) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (1536+(i-1536)))
              ·
                by_cases h7 : i < 1792
                ·
                  have h := List.all_eq_true.mp checkChunk13_pass (i-1664)
                    (List.mem_range.mpr (by omega))
                  have heq : 1664+(i-1664) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (1664+(i-1664)))
                ·
                  by_cases h8 : i < 1920
                  ·
                    have h := List.all_eq_true.mp checkChunk14_pass (i-1792)
                      (List.mem_range.mpr (by omega))
                    have heq : 1792+(i-1792) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (1792+(i-1792)))
                  ·
                    have h := List.all_eq_true.mp checkChunk15_pass (i-1920)
                      (List.mem_range.mpr (by omega))
                    have heq : 1920+(i-1920) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (1920+(i-1920)))
            ·
              by_cases h6 : i < 2432
              ·
                by_cases h7 : i < 2176
                ·
                  have h := List.all_eq_true.mp checkChunk16_pass (i-2048)
                    (List.mem_range.mpr (by omega))
                  have heq : 2048+(i-2048) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (2048+(i-2048)))
                ·
                  by_cases h8 : i < 2304
                  ·
                    have h := List.all_eq_true.mp checkChunk17_pass (i-2176)
                      (List.mem_range.mpr (by omega))
                    have heq : 2176+(i-2176) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (2176+(i-2176)))
                  ·
                    have h := List.all_eq_true.mp checkChunk18_pass (i-2304)
                      (List.mem_range.mpr (by omega))
                    have heq : 2304+(i-2304) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (2304+(i-2304)))
              ·
                by_cases h7 : i < 2560
                ·
                  have h := List.all_eq_true.mp checkChunk19_pass (i-2432)
                    (List.mem_range.mpr (by omega))
                  have heq : 2432+(i-2432) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (2432+(i-2432)))
                ·
                  by_cases h8 : i < 2688
                  ·
                    have h := List.all_eq_true.mp checkChunk20_pass (i-2560)
                      (List.mem_range.mpr (by omega))
                    have heq : 2560+(i-2560) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (2560+(i-2560)))
                  ·
                    have h := List.all_eq_true.mp checkChunk21_pass (i-2688)
                      (List.mem_range.mpr (by omega))
                    have heq : 2688+(i-2688) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (2688+(i-2688)))
        ·
          by_cases h4 : i < 4224
          ·
            by_cases h5 : i < 3456
            ·
              by_cases h6 : i < 3072
              ·
                by_cases h7 : i < 2944
                ·
                  have h := List.all_eq_true.mp checkChunk22_pass (i-2816)
                    (List.mem_range.mpr (by omega))
                  have heq : 2816+(i-2816) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (2816+(i-2816)))
                ·
                  have h := List.all_eq_true.mp checkChunk23_pass (i-2944)
                    (List.mem_range.mpr (by omega))
                  have heq : 2944+(i-2944) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (2944+(i-2944)))
              ·
                by_cases h7 : i < 3200
                ·
                  have h := List.all_eq_true.mp checkChunk24_pass (i-3072)
                    (List.mem_range.mpr (by omega))
                  have heq : 3072+(i-3072) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (3072+(i-3072)))
                ·
                  by_cases h8 : i < 3328
                  ·
                    have h := List.all_eq_true.mp checkChunk25_pass (i-3200)
                      (List.mem_range.mpr (by omega))
                    have heq : 3200+(i-3200) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (3200+(i-3200)))
                  ·
                    have h := List.all_eq_true.mp checkChunk26_pass (i-3328)
                      (List.mem_range.mpr (by omega))
                    have heq : 3328+(i-3328) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (3328+(i-3328)))
            ·
              by_cases h6 : i < 3840
              ·
                by_cases h7 : i < 3584
                ·
                  have h := List.all_eq_true.mp checkChunk27_pass (i-3456)
                    (List.mem_range.mpr (by omega))
                  have heq : 3456+(i-3456) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (3456+(i-3456)))
                ·
                  by_cases h8 : i < 3712
                  ·
                    have h := List.all_eq_true.mp checkChunk28_pass (i-3584)
                      (List.mem_range.mpr (by omega))
                    have heq : 3584+(i-3584) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (3584+(i-3584)))
                  ·
                    have h := List.all_eq_true.mp checkChunk29_pass (i-3712)
                      (List.mem_range.mpr (by omega))
                    have heq : 3712+(i-3712) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (3712+(i-3712)))
              ·
                by_cases h7 : i < 3968
                ·
                  have h := List.all_eq_true.mp checkChunk30_pass (i-3840)
                    (List.mem_range.mpr (by omega))
                  have heq : 3840+(i-3840) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (3840+(i-3840)))
                ·
                  by_cases h8 : i < 4096
                  ·
                    have h := List.all_eq_true.mp checkChunk31_pass (i-3968)
                      (List.mem_range.mpr (by omega))
                    have heq : 3968+(i-3968) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (3968+(i-3968)))
                  ·
                    have h := List.all_eq_true.mp checkChunk32_pass (i-4096)
                      (List.mem_range.mpr (by omega))
                    have heq : 4096+(i-4096) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (4096+(i-4096)))
          ·
            by_cases h5 : i < 4864
            ·
              by_cases h6 : i < 4480
              ·
                by_cases h7 : i < 4352
                ·
                  have h := List.all_eq_true.mp checkChunk33_pass (i-4224)
                    (List.mem_range.mpr (by omega))
                  have heq : 4224+(i-4224) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (4224+(i-4224)))
                ·
                  have h := List.all_eq_true.mp checkChunk34_pass (i-4352)
                    (List.mem_range.mpr (by omega))
                  have heq : 4352+(i-4352) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (4352+(i-4352)))
              ·
                by_cases h7 : i < 4608
                ·
                  have h := List.all_eq_true.mp checkChunk35_pass (i-4480)
                    (List.mem_range.mpr (by omega))
                  have heq : 4480+(i-4480) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (4480+(i-4480)))
                ·
                  by_cases h8 : i < 4736
                  ·
                    have h := List.all_eq_true.mp checkChunk36_pass (i-4608)
                      (List.mem_range.mpr (by omega))
                    have heq : 4608+(i-4608) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (4608+(i-4608)))
                  ·
                    have h := List.all_eq_true.mp checkChunk37_pass (i-4736)
                      (List.mem_range.mpr (by omega))
                    have heq : 4736+(i-4736) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (4736+(i-4736)))
            ·
              by_cases h6 : i < 5248
              ·
                by_cases h7 : i < 4992
                ·
                  have h := List.all_eq_true.mp checkChunk38_pass (i-4864)
                    (List.mem_range.mpr (by omega))
                  have heq : 4864+(i-4864) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (4864+(i-4864)))
                ·
                  by_cases h8 : i < 5120
                  ·
                    have h := List.all_eq_true.mp checkChunk39_pass (i-4992)
                      (List.mem_range.mpr (by omega))
                    have heq : 4992+(i-4992) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (4992+(i-4992)))
                  ·
                    have h := List.all_eq_true.mp checkChunk40_pass (i-5120)
                      (List.mem_range.mpr (by omega))
                    have heq : 5120+(i-5120) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (5120+(i-5120)))
              ·
                by_cases h7 : i < 5376
                ·
                  have h := List.all_eq_true.mp checkChunk41_pass (i-5248)
                    (List.mem_range.mpr (by omega))
                  have heq : 5248+(i-5248) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (5248+(i-5248)))
                ·
                  by_cases h8 : i < 5504
                  ·
                    have h := List.all_eq_true.mp checkChunk42_pass (i-5376)
                      (List.mem_range.mpr (by omega))
                    have heq : 5376+(i-5376) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (5376+(i-5376)))
                  ·
                    have h := List.all_eq_true.mp checkChunk43_pass (i-5504)
                      (List.mem_range.mpr (by omega))
                    have heq : 5504+(i-5504) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (5504+(i-5504)))
      ·
        by_cases h3 : i < 8448
        ·
          by_cases h4 : i < 7040
          ·
            by_cases h5 : i < 6272
            ·
              by_cases h6 : i < 5888
              ·
                by_cases h7 : i < 5760
                ·
                  have h := List.all_eq_true.mp checkChunk44_pass (i-5632)
                    (List.mem_range.mpr (by omega))
                  have heq : 5632+(i-5632) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (5632+(i-5632)))
                ·
                  have h := List.all_eq_true.mp checkChunk45_pass (i-5760)
                    (List.mem_range.mpr (by omega))
                  have heq : 5760+(i-5760) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (5760+(i-5760)))
              ·
                by_cases h7 : i < 6016
                ·
                  have h := List.all_eq_true.mp checkChunk46_pass (i-5888)
                    (List.mem_range.mpr (by omega))
                  have heq : 5888+(i-5888) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (5888+(i-5888)))
                ·
                  by_cases h8 : i < 6144
                  ·
                    have h := List.all_eq_true.mp checkChunk47_pass (i-6016)
                      (List.mem_range.mpr (by omega))
                    have heq : 6016+(i-6016) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (6016+(i-6016)))
                  ·
                    have h := List.all_eq_true.mp checkChunk48_pass (i-6144)
                      (List.mem_range.mpr (by omega))
                    have heq : 6144+(i-6144) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (6144+(i-6144)))
            ·
              by_cases h6 : i < 6656
              ·
                by_cases h7 : i < 6400
                ·
                  have h := List.all_eq_true.mp checkChunk49_pass (i-6272)
                    (List.mem_range.mpr (by omega))
                  have heq : 6272+(i-6272) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (6272+(i-6272)))
                ·
                  by_cases h8 : i < 6528
                  ·
                    have h := List.all_eq_true.mp checkChunk50_pass (i-6400)
                      (List.mem_range.mpr (by omega))
                    have heq : 6400+(i-6400) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (6400+(i-6400)))
                  ·
                    have h := List.all_eq_true.mp checkChunk51_pass (i-6528)
                      (List.mem_range.mpr (by omega))
                    have heq : 6528+(i-6528) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (6528+(i-6528)))
              ·
                by_cases h7 : i < 6784
                ·
                  have h := List.all_eq_true.mp checkChunk52_pass (i-6656)
                    (List.mem_range.mpr (by omega))
                  have heq : 6656+(i-6656) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (6656+(i-6656)))
                ·
                  by_cases h8 : i < 6912
                  ·
                    have h := List.all_eq_true.mp checkChunk53_pass (i-6784)
                      (List.mem_range.mpr (by omega))
                    have heq : 6784+(i-6784) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (6784+(i-6784)))
                  ·
                    have h := List.all_eq_true.mp checkChunk54_pass (i-6912)
                      (List.mem_range.mpr (by omega))
                    have heq : 6912+(i-6912) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (6912+(i-6912)))
          ·
            by_cases h5 : i < 7680
            ·
              by_cases h6 : i < 7296
              ·
                by_cases h7 : i < 7168
                ·
                  have h := List.all_eq_true.mp checkChunk55_pass (i-7040)
                    (List.mem_range.mpr (by omega))
                  have heq : 7040+(i-7040) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (7040+(i-7040)))
                ·
                  have h := List.all_eq_true.mp checkChunk56_pass (i-7168)
                    (List.mem_range.mpr (by omega))
                  have heq : 7168+(i-7168) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (7168+(i-7168)))
              ·
                by_cases h7 : i < 7424
                ·
                  have h := List.all_eq_true.mp checkChunk57_pass (i-7296)
                    (List.mem_range.mpr (by omega))
                  have heq : 7296+(i-7296) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (7296+(i-7296)))
                ·
                  by_cases h8 : i < 7552
                  ·
                    have h := List.all_eq_true.mp checkChunk58_pass (i-7424)
                      (List.mem_range.mpr (by omega))
                    have heq : 7424+(i-7424) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (7424+(i-7424)))
                  ·
                    have h := List.all_eq_true.mp checkChunk59_pass (i-7552)
                      (List.mem_range.mpr (by omega))
                    have heq : 7552+(i-7552) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (7552+(i-7552)))
            ·
              by_cases h6 : i < 8064
              ·
                by_cases h7 : i < 7808
                ·
                  have h := List.all_eq_true.mp checkChunk60_pass (i-7680)
                    (List.mem_range.mpr (by omega))
                  have heq : 7680+(i-7680) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (7680+(i-7680)))
                ·
                  by_cases h8 : i < 7936
                  ·
                    have h := List.all_eq_true.mp checkChunk61_pass (i-7808)
                      (List.mem_range.mpr (by omega))
                    have heq : 7808+(i-7808) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (7808+(i-7808)))
                  ·
                    have h := List.all_eq_true.mp checkChunk62_pass (i-7936)
                      (List.mem_range.mpr (by omega))
                    have heq : 7936+(i-7936) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (7936+(i-7936)))
              ·
                by_cases h7 : i < 8192
                ·
                  have h := List.all_eq_true.mp checkChunk63_pass (i-8064)
                    (List.mem_range.mpr (by omega))
                  have heq : 8064+(i-8064) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (8064+(i-8064)))
                ·
                  by_cases h8 : i < 8320
                  ·
                    have h := List.all_eq_true.mp checkChunk64_pass (i-8192)
                      (List.mem_range.mpr (by omega))
                    have heq : 8192+(i-8192) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (8192+(i-8192)))
                  ·
                    have h := List.all_eq_true.mp checkChunk65_pass (i-8320)
                      (List.mem_range.mpr (by omega))
                    have heq : 8320+(i-8320) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (8320+(i-8320)))
        ·
          by_cases h4 : i < 9856
          ·
            by_cases h5 : i < 9088
            ·
              by_cases h6 : i < 8704
              ·
                by_cases h7 : i < 8576
                ·
                  have h := List.all_eq_true.mp checkChunk66_pass (i-8448)
                    (List.mem_range.mpr (by omega))
                  have heq : 8448+(i-8448) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (8448+(i-8448)))
                ·
                  have h := List.all_eq_true.mp checkChunk67_pass (i-8576)
                    (List.mem_range.mpr (by omega))
                  have heq : 8576+(i-8576) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (8576+(i-8576)))
              ·
                by_cases h7 : i < 8832
                ·
                  have h := List.all_eq_true.mp checkChunk68_pass (i-8704)
                    (List.mem_range.mpr (by omega))
                  have heq : 8704+(i-8704) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (8704+(i-8704)))
                ·
                  by_cases h8 : i < 8960
                  ·
                    have h := List.all_eq_true.mp checkChunk69_pass (i-8832)
                      (List.mem_range.mpr (by omega))
                    have heq : 8832+(i-8832) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (8832+(i-8832)))
                  ·
                    have h := List.all_eq_true.mp checkChunk70_pass (i-8960)
                      (List.mem_range.mpr (by omega))
                    have heq : 8960+(i-8960) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (8960+(i-8960)))
            ·
              by_cases h6 : i < 9472
              ·
                by_cases h7 : i < 9216
                ·
                  have h := List.all_eq_true.mp checkChunk71_pass (i-9088)
                    (List.mem_range.mpr (by omega))
                  have heq : 9088+(i-9088) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (9088+(i-9088)))
                ·
                  by_cases h8 : i < 9344
                  ·
                    have h := List.all_eq_true.mp checkChunk72_pass (i-9216)
                      (List.mem_range.mpr (by omega))
                    have heq : 9216+(i-9216) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (9216+(i-9216)))
                  ·
                    have h := List.all_eq_true.mp checkChunk73_pass (i-9344)
                      (List.mem_range.mpr (by omega))
                    have heq : 9344+(i-9344) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (9344+(i-9344)))
              ·
                by_cases h7 : i < 9600
                ·
                  have h := List.all_eq_true.mp checkChunk74_pass (i-9472)
                    (List.mem_range.mpr (by omega))
                  have heq : 9472+(i-9472) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (9472+(i-9472)))
                ·
                  by_cases h8 : i < 9728
                  ·
                    have h := List.all_eq_true.mp checkChunk75_pass (i-9600)
                      (List.mem_range.mpr (by omega))
                    have heq : 9600+(i-9600) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (9600+(i-9600)))
                  ·
                    have h := List.all_eq_true.mp checkChunk76_pass (i-9728)
                      (List.mem_range.mpr (by omega))
                    have heq : 9728+(i-9728) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (9728+(i-9728)))
          ·
            by_cases h5 : i < 10624
            ·
              by_cases h6 : i < 10240
              ·
                by_cases h7 : i < 9984
                ·
                  have h := List.all_eq_true.mp checkChunk77_pass (i-9856)
                    (List.mem_range.mpr (by omega))
                  have heq : 9856+(i-9856) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (9856+(i-9856)))
                ·
                  by_cases h8 : i < 10112
                  ·
                    have h := List.all_eq_true.mp checkChunk78_pass (i-9984)
                      (List.mem_range.mpr (by omega))
                    have heq : 9984+(i-9984) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (9984+(i-9984)))
                  ·
                    have h := List.all_eq_true.mp checkChunk79_pass (i-10112)
                      (List.mem_range.mpr (by omega))
                    have heq : 10112+(i-10112) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (10112+(i-10112)))
              ·
                by_cases h7 : i < 10368
                ·
                  have h := List.all_eq_true.mp checkChunk80_pass (i-10240)
                    (List.mem_range.mpr (by omega))
                  have heq : 10240+(i-10240) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (10240+(i-10240)))
                ·
                  by_cases h8 : i < 10496
                  ·
                    have h := List.all_eq_true.mp checkChunk81_pass (i-10368)
                      (List.mem_range.mpr (by omega))
                    have heq : 10368+(i-10368) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (10368+(i-10368)))
                  ·
                    have h := List.all_eq_true.mp checkChunk82_pass (i-10496)
                      (List.mem_range.mpr (by omega))
                    have heq : 10496+(i-10496) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (10496+(i-10496)))
            ·
              by_cases h6 : i < 11008
              ·
                by_cases h7 : i < 10752
                ·
                  have h := List.all_eq_true.mp checkChunk83_pass (i-10624)
                    (List.mem_range.mpr (by omega))
                  have heq : 10624+(i-10624) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (10624+(i-10624)))
                ·
                  by_cases h8 : i < 10880
                  ·
                    have h := List.all_eq_true.mp checkChunk84_pass (i-10752)
                      (List.mem_range.mpr (by omega))
                    have heq : 10752+(i-10752) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (10752+(i-10752)))
                  ·
                    have h := List.all_eq_true.mp checkChunk85_pass (i-10880)
                      (List.mem_range.mpr (by omega))
                    have heq : 10880+(i-10880) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (10880+(i-10880)))
              ·
                by_cases h7 : i < 11136
                ·
                  have h := List.all_eq_true.mp checkChunk86_pass (i-11008)
                    (List.mem_range.mpr (by omega))
                  have heq : 11008+(i-11008) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (11008+(i-11008)))
                ·
                  by_cases h8 : i < 11264
                  ·
                    have h := List.all_eq_true.mp checkChunk87_pass (i-11136)
                      (List.mem_range.mpr (by omega))
                    have heq : 11136+(i-11136) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (11136+(i-11136)))
                  ·
                    have h := List.all_eq_true.mp checkChunk88_pass (i-11264)
                      (List.mem_range.mpr (by omega))
                    have heq : 11264+(i-11264) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (11264+(i-11264)))
    ·
      by_cases h2 : i < 17024
      ·
        by_cases h3 : i < 14208
        ·
          by_cases h4 : i < 12800
          ·
            by_cases h5 : i < 12032
            ·
              by_cases h6 : i < 11648
              ·
                by_cases h7 : i < 11520
                ·
                  have h := List.all_eq_true.mp checkChunk89_pass (i-11392)
                    (List.mem_range.mpr (by omega))
                  have heq : 11392+(i-11392) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (11392+(i-11392)))
                ·
                  have h := List.all_eq_true.mp checkChunk90_pass (i-11520)
                    (List.mem_range.mpr (by omega))
                  have heq : 11520+(i-11520) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (11520+(i-11520)))
              ·
                by_cases h7 : i < 11776
                ·
                  have h := List.all_eq_true.mp checkChunk91_pass (i-11648)
                    (List.mem_range.mpr (by omega))
                  have heq : 11648+(i-11648) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (11648+(i-11648)))
                ·
                  by_cases h8 : i < 11904
                  ·
                    have h := List.all_eq_true.mp checkChunk92_pass (i-11776)
                      (List.mem_range.mpr (by omega))
                    have heq : 11776+(i-11776) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (11776+(i-11776)))
                  ·
                    have h := List.all_eq_true.mp checkChunk93_pass (i-11904)
                      (List.mem_range.mpr (by omega))
                    have heq : 11904+(i-11904) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (11904+(i-11904)))
            ·
              by_cases h6 : i < 12416
              ·
                by_cases h7 : i < 12160
                ·
                  have h := List.all_eq_true.mp checkChunk94_pass (i-12032)
                    (List.mem_range.mpr (by omega))
                  have heq : 12032+(i-12032) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (12032+(i-12032)))
                ·
                  by_cases h8 : i < 12288
                  ·
                    have h := List.all_eq_true.mp checkChunk95_pass (i-12160)
                      (List.mem_range.mpr (by omega))
                    have heq : 12160+(i-12160) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (12160+(i-12160)))
                  ·
                    have h := List.all_eq_true.mp checkChunk96_pass (i-12288)
                      (List.mem_range.mpr (by omega))
                    have heq : 12288+(i-12288) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (12288+(i-12288)))
              ·
                by_cases h7 : i < 12544
                ·
                  have h := List.all_eq_true.mp checkChunk97_pass (i-12416)
                    (List.mem_range.mpr (by omega))
                  have heq : 12416+(i-12416) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (12416+(i-12416)))
                ·
                  by_cases h8 : i < 12672
                  ·
                    have h := List.all_eq_true.mp checkChunk98_pass (i-12544)
                      (List.mem_range.mpr (by omega))
                    have heq : 12544+(i-12544) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (12544+(i-12544)))
                  ·
                    have h := List.all_eq_true.mp checkChunk99_pass (i-12672)
                      (List.mem_range.mpr (by omega))
                    have heq : 12672+(i-12672) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (12672+(i-12672)))
          ·
            by_cases h5 : i < 13440
            ·
              by_cases h6 : i < 13056
              ·
                by_cases h7 : i < 12928
                ·
                  have h := List.all_eq_true.mp checkChunk100_pass (i-12800)
                    (List.mem_range.mpr (by omega))
                  have heq : 12800+(i-12800) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (12800+(i-12800)))
                ·
                  have h := List.all_eq_true.mp checkChunk101_pass (i-12928)
                    (List.mem_range.mpr (by omega))
                  have heq : 12928+(i-12928) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (12928+(i-12928)))
              ·
                by_cases h7 : i < 13184
                ·
                  have h := List.all_eq_true.mp checkChunk102_pass (i-13056)
                    (List.mem_range.mpr (by omega))
                  have heq : 13056+(i-13056) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (13056+(i-13056)))
                ·
                  by_cases h8 : i < 13312
                  ·
                    have h := List.all_eq_true.mp checkChunk103_pass (i-13184)
                      (List.mem_range.mpr (by omega))
                    have heq : 13184+(i-13184) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (13184+(i-13184)))
                  ·
                    have h := List.all_eq_true.mp checkChunk104_pass (i-13312)
                      (List.mem_range.mpr (by omega))
                    have heq : 13312+(i-13312) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (13312+(i-13312)))
            ·
              by_cases h6 : i < 13824
              ·
                by_cases h7 : i < 13568
                ·
                  have h := List.all_eq_true.mp checkChunk105_pass (i-13440)
                    (List.mem_range.mpr (by omega))
                  have heq : 13440+(i-13440) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (13440+(i-13440)))
                ·
                  by_cases h8 : i < 13696
                  ·
                    have h := List.all_eq_true.mp checkChunk106_pass (i-13568)
                      (List.mem_range.mpr (by omega))
                    have heq : 13568+(i-13568) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (13568+(i-13568)))
                  ·
                    have h := List.all_eq_true.mp checkChunk107_pass (i-13696)
                      (List.mem_range.mpr (by omega))
                    have heq : 13696+(i-13696) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (13696+(i-13696)))
              ·
                by_cases h7 : i < 13952
                ·
                  have h := List.all_eq_true.mp checkChunk108_pass (i-13824)
                    (List.mem_range.mpr (by omega))
                  have heq : 13824+(i-13824) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (13824+(i-13824)))
                ·
                  by_cases h8 : i < 14080
                  ·
                    have h := List.all_eq_true.mp checkChunk109_pass (i-13952)
                      (List.mem_range.mpr (by omega))
                    have heq : 13952+(i-13952) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (13952+(i-13952)))
                  ·
                    have h := List.all_eq_true.mp checkChunk110_pass (i-14080)
                      (List.mem_range.mpr (by omega))
                    have heq : 14080+(i-14080) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (14080+(i-14080)))
        ·
          by_cases h4 : i < 15616
          ·
            by_cases h5 : i < 14848
            ·
              by_cases h6 : i < 14464
              ·
                by_cases h7 : i < 14336
                ·
                  have h := List.all_eq_true.mp checkChunk111_pass (i-14208)
                    (List.mem_range.mpr (by omega))
                  have heq : 14208+(i-14208) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (14208+(i-14208)))
                ·
                  have h := List.all_eq_true.mp checkChunk112_pass (i-14336)
                    (List.mem_range.mpr (by omega))
                  have heq : 14336+(i-14336) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (14336+(i-14336)))
              ·
                by_cases h7 : i < 14592
                ·
                  have h := List.all_eq_true.mp checkChunk113_pass (i-14464)
                    (List.mem_range.mpr (by omega))
                  have heq : 14464+(i-14464) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (14464+(i-14464)))
                ·
                  by_cases h8 : i < 14720
                  ·
                    have h := List.all_eq_true.mp checkChunk114_pass (i-14592)
                      (List.mem_range.mpr (by omega))
                    have heq : 14592+(i-14592) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (14592+(i-14592)))
                  ·
                    have h := List.all_eq_true.mp checkChunk115_pass (i-14720)
                      (List.mem_range.mpr (by omega))
                    have heq : 14720+(i-14720) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (14720+(i-14720)))
            ·
              by_cases h6 : i < 15232
              ·
                by_cases h7 : i < 14976
                ·
                  have h := List.all_eq_true.mp checkChunk116_pass (i-14848)
                    (List.mem_range.mpr (by omega))
                  have heq : 14848+(i-14848) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (14848+(i-14848)))
                ·
                  by_cases h8 : i < 15104
                  ·
                    have h := List.all_eq_true.mp checkChunk117_pass (i-14976)
                      (List.mem_range.mpr (by omega))
                    have heq : 14976+(i-14976) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (14976+(i-14976)))
                  ·
                    have h := List.all_eq_true.mp checkChunk118_pass (i-15104)
                      (List.mem_range.mpr (by omega))
                    have heq : 15104+(i-15104) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (15104+(i-15104)))
              ·
                by_cases h7 : i < 15360
                ·
                  have h := List.all_eq_true.mp checkChunk119_pass (i-15232)
                    (List.mem_range.mpr (by omega))
                  have heq : 15232+(i-15232) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (15232+(i-15232)))
                ·
                  by_cases h8 : i < 15488
                  ·
                    have h := List.all_eq_true.mp checkChunk120_pass (i-15360)
                      (List.mem_range.mpr (by omega))
                    have heq : 15360+(i-15360) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (15360+(i-15360)))
                  ·
                    have h := List.all_eq_true.mp checkChunk121_pass (i-15488)
                      (List.mem_range.mpr (by omega))
                    have heq : 15488+(i-15488) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (15488+(i-15488)))
          ·
            by_cases h5 : i < 16256
            ·
              by_cases h6 : i < 15872
              ·
                by_cases h7 : i < 15744
                ·
                  have h := List.all_eq_true.mp checkChunk122_pass (i-15616)
                    (List.mem_range.mpr (by omega))
                  have heq : 15616+(i-15616) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (15616+(i-15616)))
                ·
                  have h := List.all_eq_true.mp checkChunk123_pass (i-15744)
                    (List.mem_range.mpr (by omega))
                  have heq : 15744+(i-15744) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (15744+(i-15744)))
              ·
                by_cases h7 : i < 16000
                ·
                  have h := List.all_eq_true.mp checkChunk124_pass (i-15872)
                    (List.mem_range.mpr (by omega))
                  have heq : 15872+(i-15872) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (15872+(i-15872)))
                ·
                  by_cases h8 : i < 16128
                  ·
                    have h := List.all_eq_true.mp checkChunk125_pass (i-16000)
                      (List.mem_range.mpr (by omega))
                    have heq : 16000+(i-16000) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (16000+(i-16000)))
                  ·
                    have h := List.all_eq_true.mp checkChunk126_pass (i-16128)
                      (List.mem_range.mpr (by omega))
                    have heq : 16128+(i-16128) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (16128+(i-16128)))
            ·
              by_cases h6 : i < 16640
              ·
                by_cases h7 : i < 16384
                ·
                  have h := List.all_eq_true.mp checkChunk127_pass (i-16256)
                    (List.mem_range.mpr (by omega))
                  have heq : 16256+(i-16256) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (16256+(i-16256)))
                ·
                  by_cases h8 : i < 16512
                  ·
                    have h := List.all_eq_true.mp checkChunk128_pass (i-16384)
                      (List.mem_range.mpr (by omega))
                    have heq : 16384+(i-16384) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (16384+(i-16384)))
                  ·
                    have h := List.all_eq_true.mp checkChunk129_pass (i-16512)
                      (List.mem_range.mpr (by omega))
                    have heq : 16512+(i-16512) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (16512+(i-16512)))
              ·
                by_cases h7 : i < 16768
                ·
                  have h := List.all_eq_true.mp checkChunk130_pass (i-16640)
                    (List.mem_range.mpr (by omega))
                  have heq : 16640+(i-16640) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (16640+(i-16640)))
                ·
                  by_cases h8 : i < 16896
                  ·
                    have h := List.all_eq_true.mp checkChunk131_pass (i-16768)
                      (List.mem_range.mpr (by omega))
                    have heq : 16768+(i-16768) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (16768+(i-16768)))
                  ·
                    have h := List.all_eq_true.mp checkChunk132_pass (i-16896)
                      (List.mem_range.mpr (by omega))
                    have heq : 16896+(i-16896) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (16896+(i-16896)))
      ·
        by_cases h3 : i < 19840
        ·
          by_cases h4 : i < 18432
          ·
            by_cases h5 : i < 17664
            ·
              by_cases h6 : i < 17280
              ·
                by_cases h7 : i < 17152
                ·
                  have h := List.all_eq_true.mp checkChunk133_pass (i-17024)
                    (List.mem_range.mpr (by omega))
                  have heq : 17024+(i-17024) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (17024+(i-17024)))
                ·
                  have h := List.all_eq_true.mp checkChunk134_pass (i-17152)
                    (List.mem_range.mpr (by omega))
                  have heq : 17152+(i-17152) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (17152+(i-17152)))
              ·
                by_cases h7 : i < 17408
                ·
                  have h := List.all_eq_true.mp checkChunk135_pass (i-17280)
                    (List.mem_range.mpr (by omega))
                  have heq : 17280+(i-17280) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (17280+(i-17280)))
                ·
                  by_cases h8 : i < 17536
                  ·
                    have h := List.all_eq_true.mp checkChunk136_pass (i-17408)
                      (List.mem_range.mpr (by omega))
                    have heq : 17408+(i-17408) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (17408+(i-17408)))
                  ·
                    have h := List.all_eq_true.mp checkChunk137_pass (i-17536)
                      (List.mem_range.mpr (by omega))
                    have heq : 17536+(i-17536) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (17536+(i-17536)))
            ·
              by_cases h6 : i < 18048
              ·
                by_cases h7 : i < 17792
                ·
                  have h := List.all_eq_true.mp checkChunk138_pass (i-17664)
                    (List.mem_range.mpr (by omega))
                  have heq : 17664+(i-17664) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (17664+(i-17664)))
                ·
                  by_cases h8 : i < 17920
                  ·
                    have h := List.all_eq_true.mp checkChunk139_pass (i-17792)
                      (List.mem_range.mpr (by omega))
                    have heq : 17792+(i-17792) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (17792+(i-17792)))
                  ·
                    have h := List.all_eq_true.mp checkChunk140_pass (i-17920)
                      (List.mem_range.mpr (by omega))
                    have heq : 17920+(i-17920) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (17920+(i-17920)))
              ·
                by_cases h7 : i < 18176
                ·
                  have h := List.all_eq_true.mp checkChunk141_pass (i-18048)
                    (List.mem_range.mpr (by omega))
                  have heq : 18048+(i-18048) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (18048+(i-18048)))
                ·
                  by_cases h8 : i < 18304
                  ·
                    have h := List.all_eq_true.mp checkChunk142_pass (i-18176)
                      (List.mem_range.mpr (by omega))
                    have heq : 18176+(i-18176) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (18176+(i-18176)))
                  ·
                    have h := List.all_eq_true.mp checkChunk143_pass (i-18304)
                      (List.mem_range.mpr (by omega))
                    have heq : 18304+(i-18304) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (18304+(i-18304)))
          ·
            by_cases h5 : i < 19072
            ·
              by_cases h6 : i < 18688
              ·
                by_cases h7 : i < 18560
                ·
                  have h := List.all_eq_true.mp checkChunk144_pass (i-18432)
                    (List.mem_range.mpr (by omega))
                  have heq : 18432+(i-18432) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (18432+(i-18432)))
                ·
                  have h := List.all_eq_true.mp checkChunk145_pass (i-18560)
                    (List.mem_range.mpr (by omega))
                  have heq : 18560+(i-18560) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (18560+(i-18560)))
              ·
                by_cases h7 : i < 18816
                ·
                  have h := List.all_eq_true.mp checkChunk146_pass (i-18688)
                    (List.mem_range.mpr (by omega))
                  have heq : 18688+(i-18688) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (18688+(i-18688)))
                ·
                  by_cases h8 : i < 18944
                  ·
                    have h := List.all_eq_true.mp checkChunk147_pass (i-18816)
                      (List.mem_range.mpr (by omega))
                    have heq : 18816+(i-18816) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (18816+(i-18816)))
                  ·
                    have h := List.all_eq_true.mp checkChunk148_pass (i-18944)
                      (List.mem_range.mpr (by omega))
                    have heq : 18944+(i-18944) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (18944+(i-18944)))
            ·
              by_cases h6 : i < 19456
              ·
                by_cases h7 : i < 19200
                ·
                  have h := List.all_eq_true.mp checkChunk149_pass (i-19072)
                    (List.mem_range.mpr (by omega))
                  have heq : 19072+(i-19072) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (19072+(i-19072)))
                ·
                  by_cases h8 : i < 19328
                  ·
                    have h := List.all_eq_true.mp checkChunk150_pass (i-19200)
                      (List.mem_range.mpr (by omega))
                    have heq : 19200+(i-19200) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (19200+(i-19200)))
                  ·
                    have h := List.all_eq_true.mp checkChunk151_pass (i-19328)
                      (List.mem_range.mpr (by omega))
                    have heq : 19328+(i-19328) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (19328+(i-19328)))
              ·
                by_cases h7 : i < 19584
                ·
                  have h := List.all_eq_true.mp checkChunk152_pass (i-19456)
                    (List.mem_range.mpr (by omega))
                  have heq : 19456+(i-19456) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (19456+(i-19456)))
                ·
                  by_cases h8 : i < 19712
                  ·
                    have h := List.all_eq_true.mp checkChunk153_pass (i-19584)
                      (List.mem_range.mpr (by omega))
                    have heq : 19584+(i-19584) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (19584+(i-19584)))
                  ·
                    have h := List.all_eq_true.mp checkChunk154_pass (i-19712)
                      (List.mem_range.mpr (by omega))
                    have heq : 19712+(i-19712) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (19712+(i-19712)))
        ·
          by_cases h4 : i < 21248
          ·
            by_cases h5 : i < 20480
            ·
              by_cases h6 : i < 20096
              ·
                by_cases h7 : i < 19968
                ·
                  have h := List.all_eq_true.mp checkChunk155_pass (i-19840)
                    (List.mem_range.mpr (by omega))
                  have heq : 19840+(i-19840) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (19840+(i-19840)))
                ·
                  have h := List.all_eq_true.mp checkChunk156_pass (i-19968)
                    (List.mem_range.mpr (by omega))
                  have heq : 19968+(i-19968) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (19968+(i-19968)))
              ·
                by_cases h7 : i < 20224
                ·
                  have h := List.all_eq_true.mp checkChunk157_pass (i-20096)
                    (List.mem_range.mpr (by omega))
                  have heq : 20096+(i-20096) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (20096+(i-20096)))
                ·
                  by_cases h8 : i < 20352
                  ·
                    have h := List.all_eq_true.mp checkChunk158_pass (i-20224)
                      (List.mem_range.mpr (by omega))
                    have heq : 20224+(i-20224) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (20224+(i-20224)))
                  ·
                    have h := List.all_eq_true.mp checkChunk159_pass (i-20352)
                      (List.mem_range.mpr (by omega))
                    have heq : 20352+(i-20352) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (20352+(i-20352)))
            ·
              by_cases h6 : i < 20864
              ·
                by_cases h7 : i < 20608
                ·
                  have h := List.all_eq_true.mp checkChunk160_pass (i-20480)
                    (List.mem_range.mpr (by omega))
                  have heq : 20480+(i-20480) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (20480+(i-20480)))
                ·
                  by_cases h8 : i < 20736
                  ·
                    have h := List.all_eq_true.mp checkChunk161_pass (i-20608)
                      (List.mem_range.mpr (by omega))
                    have heq : 20608+(i-20608) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (20608+(i-20608)))
                  ·
                    have h := List.all_eq_true.mp checkChunk162_pass (i-20736)
                      (List.mem_range.mpr (by omega))
                    have heq : 20736+(i-20736) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (20736+(i-20736)))
              ·
                by_cases h7 : i < 20992
                ·
                  have h := List.all_eq_true.mp checkChunk163_pass (i-20864)
                    (List.mem_range.mpr (by omega))
                  have heq : 20864+(i-20864) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (20864+(i-20864)))
                ·
                  by_cases h8 : i < 21120
                  ·
                    have h := List.all_eq_true.mp checkChunk164_pass (i-20992)
                      (List.mem_range.mpr (by omega))
                    have heq : 20992+(i-20992) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (20992+(i-20992)))
                  ·
                    have h := List.all_eq_true.mp checkChunk165_pass (i-21120)
                      (List.mem_range.mpr (by omega))
                    have heq : 21120+(i-21120) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (21120+(i-21120)))
          ·
            by_cases h5 : i < 22016
            ·
              by_cases h6 : i < 21632
              ·
                by_cases h7 : i < 21376
                ·
                  have h := List.all_eq_true.mp checkChunk166_pass (i-21248)
                    (List.mem_range.mpr (by omega))
                  have heq : 21248+(i-21248) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (21248+(i-21248)))
                ·
                  by_cases h8 : i < 21504
                  ·
                    have h := List.all_eq_true.mp checkChunk167_pass (i-21376)
                      (List.mem_range.mpr (by omega))
                    have heq : 21376+(i-21376) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (21376+(i-21376)))
                  ·
                    have h := List.all_eq_true.mp checkChunk168_pass (i-21504)
                      (List.mem_range.mpr (by omega))
                    have heq : 21504+(i-21504) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (21504+(i-21504)))
              ·
                by_cases h7 : i < 21760
                ·
                  have h := List.all_eq_true.mp checkChunk169_pass (i-21632)
                    (List.mem_range.mpr (by omega))
                  have heq : 21632+(i-21632) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (21632+(i-21632)))
                ·
                  by_cases h8 : i < 21888
                  ·
                    have h := List.all_eq_true.mp checkChunk170_pass (i-21760)
                      (List.mem_range.mpr (by omega))
                    have heq : 21760+(i-21760) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (21760+(i-21760)))
                  ·
                    have h := List.all_eq_true.mp checkChunk171_pass (i-21888)
                      (List.mem_range.mpr (by omega))
                    have heq : 21888+(i-21888) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (21888+(i-21888)))
            ·
              by_cases h6 : i < 22400
              ·
                by_cases h7 : i < 22144
                ·
                  have h := List.all_eq_true.mp checkChunk172_pass (i-22016)
                    (List.mem_range.mpr (by omega))
                  have heq : 22016+(i-22016) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (22016+(i-22016)))
                ·
                  by_cases h8 : i < 22272
                  ·
                    have h := List.all_eq_true.mp checkChunk173_pass (i-22144)
                      (List.mem_range.mpr (by omega))
                    have heq : 22144+(i-22144) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (22144+(i-22144)))
                  ·
                    have h := List.all_eq_true.mp checkChunk174_pass (i-22272)
                      (List.mem_range.mpr (by omega))
                    have heq : 22272+(i-22272) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (22272+(i-22272)))
              ·
                by_cases h7 : i < 22528
                ·
                  have h := List.all_eq_true.mp checkChunk175_pass (i-22400)
                    (List.mem_range.mpr (by omega))
                  have heq : 22400+(i-22400) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (22400+(i-22400)))
                ·
                  by_cases h8 : i < 22656
                  ·
                    have h := List.all_eq_true.mp checkChunk176_pass (i-22528)
                      (List.mem_range.mpr (by omega))
                    have heq : 22528+(i-22528) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (22528+(i-22528)))
                  ·
                    have h := List.all_eq_true.mp checkChunk177_pass (i-22656)
                      (List.mem_range.mpr (by omega))
                    have heq : 22656+(i-22656) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (22656+(i-22656)))
  ·
    by_cases h1 : i < 34176
    ·
      by_cases h2 : i < 28416
      ·
        by_cases h3 : i < 25600
        ·
          by_cases h4 : i < 24192
          ·
            by_cases h5 : i < 23424
            ·
              by_cases h6 : i < 23040
              ·
                by_cases h7 : i < 22912
                ·
                  have h := List.all_eq_true.mp checkChunk178_pass (i-22784)
                    (List.mem_range.mpr (by omega))
                  have heq : 22784+(i-22784) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (22784+(i-22784)))
                ·
                  have h := List.all_eq_true.mp checkChunk179_pass (i-22912)
                    (List.mem_range.mpr (by omega))
                  have heq : 22912+(i-22912) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (22912+(i-22912)))
              ·
                by_cases h7 : i < 23168
                ·
                  have h := List.all_eq_true.mp checkChunk180_pass (i-23040)
                    (List.mem_range.mpr (by omega))
                  have heq : 23040+(i-23040) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (23040+(i-23040)))
                ·
                  by_cases h8 : i < 23296
                  ·
                    have h := List.all_eq_true.mp checkChunk181_pass (i-23168)
                      (List.mem_range.mpr (by omega))
                    have heq : 23168+(i-23168) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (23168+(i-23168)))
                  ·
                    have h := List.all_eq_true.mp checkChunk182_pass (i-23296)
                      (List.mem_range.mpr (by omega))
                    have heq : 23296+(i-23296) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (23296+(i-23296)))
            ·
              by_cases h6 : i < 23808
              ·
                by_cases h7 : i < 23552
                ·
                  have h := List.all_eq_true.mp checkChunk183_pass (i-23424)
                    (List.mem_range.mpr (by omega))
                  have heq : 23424+(i-23424) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (23424+(i-23424)))
                ·
                  by_cases h8 : i < 23680
                  ·
                    have h := List.all_eq_true.mp checkChunk184_pass (i-23552)
                      (List.mem_range.mpr (by omega))
                    have heq : 23552+(i-23552) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (23552+(i-23552)))
                  ·
                    have h := List.all_eq_true.mp checkChunk185_pass (i-23680)
                      (List.mem_range.mpr (by omega))
                    have heq : 23680+(i-23680) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (23680+(i-23680)))
              ·
                by_cases h7 : i < 23936
                ·
                  have h := List.all_eq_true.mp checkChunk186_pass (i-23808)
                    (List.mem_range.mpr (by omega))
                  have heq : 23808+(i-23808) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (23808+(i-23808)))
                ·
                  by_cases h8 : i < 24064
                  ·
                    have h := List.all_eq_true.mp checkChunk187_pass (i-23936)
                      (List.mem_range.mpr (by omega))
                    have heq : 23936+(i-23936) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (23936+(i-23936)))
                  ·
                    have h := List.all_eq_true.mp checkChunk188_pass (i-24064)
                      (List.mem_range.mpr (by omega))
                    have heq : 24064+(i-24064) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (24064+(i-24064)))
          ·
            by_cases h5 : i < 24832
            ·
              by_cases h6 : i < 24448
              ·
                by_cases h7 : i < 24320
                ·
                  have h := List.all_eq_true.mp checkChunk189_pass (i-24192)
                    (List.mem_range.mpr (by omega))
                  have heq : 24192+(i-24192) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (24192+(i-24192)))
                ·
                  have h := List.all_eq_true.mp checkChunk190_pass (i-24320)
                    (List.mem_range.mpr (by omega))
                  have heq : 24320+(i-24320) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (24320+(i-24320)))
              ·
                by_cases h7 : i < 24576
                ·
                  have h := List.all_eq_true.mp checkChunk191_pass (i-24448)
                    (List.mem_range.mpr (by omega))
                  have heq : 24448+(i-24448) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (24448+(i-24448)))
                ·
                  by_cases h8 : i < 24704
                  ·
                    have h := List.all_eq_true.mp checkChunk192_pass (i-24576)
                      (List.mem_range.mpr (by omega))
                    have heq : 24576+(i-24576) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (24576+(i-24576)))
                  ·
                    have h := List.all_eq_true.mp checkChunk193_pass (i-24704)
                      (List.mem_range.mpr (by omega))
                    have heq : 24704+(i-24704) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (24704+(i-24704)))
            ·
              by_cases h6 : i < 25216
              ·
                by_cases h7 : i < 24960
                ·
                  have h := List.all_eq_true.mp checkChunk194_pass (i-24832)
                    (List.mem_range.mpr (by omega))
                  have heq : 24832+(i-24832) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (24832+(i-24832)))
                ·
                  by_cases h8 : i < 25088
                  ·
                    have h := List.all_eq_true.mp checkChunk195_pass (i-24960)
                      (List.mem_range.mpr (by omega))
                    have heq : 24960+(i-24960) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (24960+(i-24960)))
                  ·
                    have h := List.all_eq_true.mp checkChunk196_pass (i-25088)
                      (List.mem_range.mpr (by omega))
                    have heq : 25088+(i-25088) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (25088+(i-25088)))
              ·
                by_cases h7 : i < 25344
                ·
                  have h := List.all_eq_true.mp checkChunk197_pass (i-25216)
                    (List.mem_range.mpr (by omega))
                  have heq : 25216+(i-25216) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (25216+(i-25216)))
                ·
                  by_cases h8 : i < 25472
                  ·
                    have h := List.all_eq_true.mp checkChunk198_pass (i-25344)
                      (List.mem_range.mpr (by omega))
                    have heq : 25344+(i-25344) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (25344+(i-25344)))
                  ·
                    have h := List.all_eq_true.mp checkChunk199_pass (i-25472)
                      (List.mem_range.mpr (by omega))
                    have heq : 25472+(i-25472) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (25472+(i-25472)))
        ·
          by_cases h4 : i < 27008
          ·
            by_cases h5 : i < 26240
            ·
              by_cases h6 : i < 25856
              ·
                by_cases h7 : i < 25728
                ·
                  have h := List.all_eq_true.mp checkChunk200_pass (i-25600)
                    (List.mem_range.mpr (by omega))
                  have heq : 25600+(i-25600) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (25600+(i-25600)))
                ·
                  have h := List.all_eq_true.mp checkChunk201_pass (i-25728)
                    (List.mem_range.mpr (by omega))
                  have heq : 25728+(i-25728) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (25728+(i-25728)))
              ·
                by_cases h7 : i < 25984
                ·
                  have h := List.all_eq_true.mp checkChunk202_pass (i-25856)
                    (List.mem_range.mpr (by omega))
                  have heq : 25856+(i-25856) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (25856+(i-25856)))
                ·
                  by_cases h8 : i < 26112
                  ·
                    have h := List.all_eq_true.mp checkChunk203_pass (i-25984)
                      (List.mem_range.mpr (by omega))
                    have heq : 25984+(i-25984) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (25984+(i-25984)))
                  ·
                    have h := List.all_eq_true.mp checkChunk204_pass (i-26112)
                      (List.mem_range.mpr (by omega))
                    have heq : 26112+(i-26112) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (26112+(i-26112)))
            ·
              by_cases h6 : i < 26624
              ·
                by_cases h7 : i < 26368
                ·
                  have h := List.all_eq_true.mp checkChunk205_pass (i-26240)
                    (List.mem_range.mpr (by omega))
                  have heq : 26240+(i-26240) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (26240+(i-26240)))
                ·
                  by_cases h8 : i < 26496
                  ·
                    have h := List.all_eq_true.mp checkChunk206_pass (i-26368)
                      (List.mem_range.mpr (by omega))
                    have heq : 26368+(i-26368) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (26368+(i-26368)))
                  ·
                    have h := List.all_eq_true.mp checkChunk207_pass (i-26496)
                      (List.mem_range.mpr (by omega))
                    have heq : 26496+(i-26496) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (26496+(i-26496)))
              ·
                by_cases h7 : i < 26752
                ·
                  have h := List.all_eq_true.mp checkChunk208_pass (i-26624)
                    (List.mem_range.mpr (by omega))
                  have heq : 26624+(i-26624) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (26624+(i-26624)))
                ·
                  by_cases h8 : i < 26880
                  ·
                    have h := List.all_eq_true.mp checkChunk209_pass (i-26752)
                      (List.mem_range.mpr (by omega))
                    have heq : 26752+(i-26752) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (26752+(i-26752)))
                  ·
                    have h := List.all_eq_true.mp checkChunk210_pass (i-26880)
                      (List.mem_range.mpr (by omega))
                    have heq : 26880+(i-26880) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (26880+(i-26880)))
          ·
            by_cases h5 : i < 27648
            ·
              by_cases h6 : i < 27264
              ·
                by_cases h7 : i < 27136
                ·
                  have h := List.all_eq_true.mp checkChunk211_pass (i-27008)
                    (List.mem_range.mpr (by omega))
                  have heq : 27008+(i-27008) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (27008+(i-27008)))
                ·
                  have h := List.all_eq_true.mp checkChunk212_pass (i-27136)
                    (List.mem_range.mpr (by omega))
                  have heq : 27136+(i-27136) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (27136+(i-27136)))
              ·
                by_cases h7 : i < 27392
                ·
                  have h := List.all_eq_true.mp checkChunk213_pass (i-27264)
                    (List.mem_range.mpr (by omega))
                  have heq : 27264+(i-27264) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (27264+(i-27264)))
                ·
                  by_cases h8 : i < 27520
                  ·
                    have h := List.all_eq_true.mp checkChunk214_pass (i-27392)
                      (List.mem_range.mpr (by omega))
                    have heq : 27392+(i-27392) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (27392+(i-27392)))
                  ·
                    have h := List.all_eq_true.mp checkChunk215_pass (i-27520)
                      (List.mem_range.mpr (by omega))
                    have heq : 27520+(i-27520) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (27520+(i-27520)))
            ·
              by_cases h6 : i < 28032
              ·
                by_cases h7 : i < 27776
                ·
                  have h := List.all_eq_true.mp checkChunk216_pass (i-27648)
                    (List.mem_range.mpr (by omega))
                  have heq : 27648+(i-27648) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (27648+(i-27648)))
                ·
                  by_cases h8 : i < 27904
                  ·
                    have h := List.all_eq_true.mp checkChunk217_pass (i-27776)
                      (List.mem_range.mpr (by omega))
                    have heq : 27776+(i-27776) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (27776+(i-27776)))
                  ·
                    have h := List.all_eq_true.mp checkChunk218_pass (i-27904)
                      (List.mem_range.mpr (by omega))
                    have heq : 27904+(i-27904) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (27904+(i-27904)))
              ·
                by_cases h7 : i < 28160
                ·
                  have h := List.all_eq_true.mp checkChunk219_pass (i-28032)
                    (List.mem_range.mpr (by omega))
                  have heq : 28032+(i-28032) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (28032+(i-28032)))
                ·
                  by_cases h8 : i < 28288
                  ·
                    have h := List.all_eq_true.mp checkChunk220_pass (i-28160)
                      (List.mem_range.mpr (by omega))
                    have heq : 28160+(i-28160) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (28160+(i-28160)))
                  ·
                    have h := List.all_eq_true.mp checkChunk221_pass (i-28288)
                      (List.mem_range.mpr (by omega))
                    have heq : 28288+(i-28288) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (28288+(i-28288)))
      ·
        by_cases h3 : i < 31232
        ·
          by_cases h4 : i < 29824
          ·
            by_cases h5 : i < 29056
            ·
              by_cases h6 : i < 28672
              ·
                by_cases h7 : i < 28544
                ·
                  have h := List.all_eq_true.mp checkChunk222_pass (i-28416)
                    (List.mem_range.mpr (by omega))
                  have heq : 28416+(i-28416) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (28416+(i-28416)))
                ·
                  have h := List.all_eq_true.mp checkChunk223_pass (i-28544)
                    (List.mem_range.mpr (by omega))
                  have heq : 28544+(i-28544) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (28544+(i-28544)))
              ·
                by_cases h7 : i < 28800
                ·
                  have h := List.all_eq_true.mp checkChunk224_pass (i-28672)
                    (List.mem_range.mpr (by omega))
                  have heq : 28672+(i-28672) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (28672+(i-28672)))
                ·
                  by_cases h8 : i < 28928
                  ·
                    have h := List.all_eq_true.mp checkChunk225_pass (i-28800)
                      (List.mem_range.mpr (by omega))
                    have heq : 28800+(i-28800) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (28800+(i-28800)))
                  ·
                    have h := List.all_eq_true.mp checkChunk226_pass (i-28928)
                      (List.mem_range.mpr (by omega))
                    have heq : 28928+(i-28928) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (28928+(i-28928)))
            ·
              by_cases h6 : i < 29440
              ·
                by_cases h7 : i < 29184
                ·
                  have h := List.all_eq_true.mp checkChunk227_pass (i-29056)
                    (List.mem_range.mpr (by omega))
                  have heq : 29056+(i-29056) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (29056+(i-29056)))
                ·
                  by_cases h8 : i < 29312
                  ·
                    have h := List.all_eq_true.mp checkChunk228_pass (i-29184)
                      (List.mem_range.mpr (by omega))
                    have heq : 29184+(i-29184) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (29184+(i-29184)))
                  ·
                    have h := List.all_eq_true.mp checkChunk229_pass (i-29312)
                      (List.mem_range.mpr (by omega))
                    have heq : 29312+(i-29312) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (29312+(i-29312)))
              ·
                by_cases h7 : i < 29568
                ·
                  have h := List.all_eq_true.mp checkChunk230_pass (i-29440)
                    (List.mem_range.mpr (by omega))
                  have heq : 29440+(i-29440) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (29440+(i-29440)))
                ·
                  by_cases h8 : i < 29696
                  ·
                    have h := List.all_eq_true.mp checkChunk231_pass (i-29568)
                      (List.mem_range.mpr (by omega))
                    have heq : 29568+(i-29568) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (29568+(i-29568)))
                  ·
                    have h := List.all_eq_true.mp checkChunk232_pass (i-29696)
                      (List.mem_range.mpr (by omega))
                    have heq : 29696+(i-29696) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (29696+(i-29696)))
          ·
            by_cases h5 : i < 30464
            ·
              by_cases h6 : i < 30080
              ·
                by_cases h7 : i < 29952
                ·
                  have h := List.all_eq_true.mp checkChunk233_pass (i-29824)
                    (List.mem_range.mpr (by omega))
                  have heq : 29824+(i-29824) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (29824+(i-29824)))
                ·
                  have h := List.all_eq_true.mp checkChunk234_pass (i-29952)
                    (List.mem_range.mpr (by omega))
                  have heq : 29952+(i-29952) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (29952+(i-29952)))
              ·
                by_cases h7 : i < 30208
                ·
                  have h := List.all_eq_true.mp checkChunk235_pass (i-30080)
                    (List.mem_range.mpr (by omega))
                  have heq : 30080+(i-30080) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (30080+(i-30080)))
                ·
                  by_cases h8 : i < 30336
                  ·
                    have h := List.all_eq_true.mp checkChunk236_pass (i-30208)
                      (List.mem_range.mpr (by omega))
                    have heq : 30208+(i-30208) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (30208+(i-30208)))
                  ·
                    have h := List.all_eq_true.mp checkChunk237_pass (i-30336)
                      (List.mem_range.mpr (by omega))
                    have heq : 30336+(i-30336) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (30336+(i-30336)))
            ·
              by_cases h6 : i < 30848
              ·
                by_cases h7 : i < 30592
                ·
                  have h := List.all_eq_true.mp checkChunk238_pass (i-30464)
                    (List.mem_range.mpr (by omega))
                  have heq : 30464+(i-30464) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (30464+(i-30464)))
                ·
                  by_cases h8 : i < 30720
                  ·
                    have h := List.all_eq_true.mp checkChunk239_pass (i-30592)
                      (List.mem_range.mpr (by omega))
                    have heq : 30592+(i-30592) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (30592+(i-30592)))
                  ·
                    have h := List.all_eq_true.mp checkChunk240_pass (i-30720)
                      (List.mem_range.mpr (by omega))
                    have heq : 30720+(i-30720) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (30720+(i-30720)))
              ·
                by_cases h7 : i < 30976
                ·
                  have h := List.all_eq_true.mp checkChunk241_pass (i-30848)
                    (List.mem_range.mpr (by omega))
                  have heq : 30848+(i-30848) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (30848+(i-30848)))
                ·
                  by_cases h8 : i < 31104
                  ·
                    have h := List.all_eq_true.mp checkChunk242_pass (i-30976)
                      (List.mem_range.mpr (by omega))
                    have heq : 30976+(i-30976) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (30976+(i-30976)))
                  ·
                    have h := List.all_eq_true.mp checkChunk243_pass (i-31104)
                      (List.mem_range.mpr (by omega))
                    have heq : 31104+(i-31104) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (31104+(i-31104)))
        ·
          by_cases h4 : i < 32640
          ·
            by_cases h5 : i < 31872
            ·
              by_cases h6 : i < 31488
              ·
                by_cases h7 : i < 31360
                ·
                  have h := List.all_eq_true.mp checkChunk244_pass (i-31232)
                    (List.mem_range.mpr (by omega))
                  have heq : 31232+(i-31232) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (31232+(i-31232)))
                ·
                  have h := List.all_eq_true.mp checkChunk245_pass (i-31360)
                    (List.mem_range.mpr (by omega))
                  have heq : 31360+(i-31360) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (31360+(i-31360)))
              ·
                by_cases h7 : i < 31616
                ·
                  have h := List.all_eq_true.mp checkChunk246_pass (i-31488)
                    (List.mem_range.mpr (by omega))
                  have heq : 31488+(i-31488) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (31488+(i-31488)))
                ·
                  by_cases h8 : i < 31744
                  ·
                    have h := List.all_eq_true.mp checkChunk247_pass (i-31616)
                      (List.mem_range.mpr (by omega))
                    have heq : 31616+(i-31616) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (31616+(i-31616)))
                  ·
                    have h := List.all_eq_true.mp checkChunk248_pass (i-31744)
                      (List.mem_range.mpr (by omega))
                    have heq : 31744+(i-31744) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (31744+(i-31744)))
            ·
              by_cases h6 : i < 32256
              ·
                by_cases h7 : i < 32000
                ·
                  have h := List.all_eq_true.mp checkChunk249_pass (i-31872)
                    (List.mem_range.mpr (by omega))
                  have heq : 31872+(i-31872) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (31872+(i-31872)))
                ·
                  by_cases h8 : i < 32128
                  ·
                    have h := List.all_eq_true.mp checkChunk250_pass (i-32000)
                      (List.mem_range.mpr (by omega))
                    have heq : 32000+(i-32000) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (32000+(i-32000)))
                  ·
                    have h := List.all_eq_true.mp checkChunk251_pass (i-32128)
                      (List.mem_range.mpr (by omega))
                    have heq : 32128+(i-32128) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (32128+(i-32128)))
              ·
                by_cases h7 : i < 32384
                ·
                  have h := List.all_eq_true.mp checkChunk252_pass (i-32256)
                    (List.mem_range.mpr (by omega))
                  have heq : 32256+(i-32256) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (32256+(i-32256)))
                ·
                  by_cases h8 : i < 32512
                  ·
                    have h := List.all_eq_true.mp checkChunk253_pass (i-32384)
                      (List.mem_range.mpr (by omega))
                    have heq : 32384+(i-32384) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (32384+(i-32384)))
                  ·
                    have h := List.all_eq_true.mp checkChunk254_pass (i-32512)
                      (List.mem_range.mpr (by omega))
                    have heq : 32512+(i-32512) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (32512+(i-32512)))
          ·
            by_cases h5 : i < 33408
            ·
              by_cases h6 : i < 33024
              ·
                by_cases h7 : i < 32768
                ·
                  have h := List.all_eq_true.mp checkChunk255_pass (i-32640)
                    (List.mem_range.mpr (by omega))
                  have heq : 32640+(i-32640) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (32640+(i-32640)))
                ·
                  by_cases h8 : i < 32896
                  ·
                    have h := List.all_eq_true.mp checkChunk256_pass (i-32768)
                      (List.mem_range.mpr (by omega))
                    have heq : 32768+(i-32768) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (32768+(i-32768)))
                  ·
                    have h := List.all_eq_true.mp checkChunk257_pass (i-32896)
                      (List.mem_range.mpr (by omega))
                    have heq : 32896+(i-32896) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (32896+(i-32896)))
              ·
                by_cases h7 : i < 33152
                ·
                  have h := List.all_eq_true.mp checkChunk258_pass (i-33024)
                    (List.mem_range.mpr (by omega))
                  have heq : 33024+(i-33024) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (33024+(i-33024)))
                ·
                  by_cases h8 : i < 33280
                  ·
                    have h := List.all_eq_true.mp checkChunk259_pass (i-33152)
                      (List.mem_range.mpr (by omega))
                    have heq : 33152+(i-33152) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (33152+(i-33152)))
                  ·
                    have h := List.all_eq_true.mp checkChunk260_pass (i-33280)
                      (List.mem_range.mpr (by omega))
                    have heq : 33280+(i-33280) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (33280+(i-33280)))
            ·
              by_cases h6 : i < 33792
              ·
                by_cases h7 : i < 33536
                ·
                  have h := List.all_eq_true.mp checkChunk261_pass (i-33408)
                    (List.mem_range.mpr (by omega))
                  have heq : 33408+(i-33408) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (33408+(i-33408)))
                ·
                  by_cases h8 : i < 33664
                  ·
                    have h := List.all_eq_true.mp checkChunk262_pass (i-33536)
                      (List.mem_range.mpr (by omega))
                    have heq : 33536+(i-33536) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (33536+(i-33536)))
                  ·
                    have h := List.all_eq_true.mp checkChunk263_pass (i-33664)
                      (List.mem_range.mpr (by omega))
                    have heq : 33664+(i-33664) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (33664+(i-33664)))
              ·
                by_cases h7 : i < 33920
                ·
                  have h := List.all_eq_true.mp checkChunk264_pass (i-33792)
                    (List.mem_range.mpr (by omega))
                  have heq : 33792+(i-33792) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (33792+(i-33792)))
                ·
                  by_cases h8 : i < 34048
                  ·
                    have h := List.all_eq_true.mp checkChunk265_pass (i-33920)
                      (List.mem_range.mpr (by omega))
                    have heq : 33920+(i-33920) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (33920+(i-33920)))
                  ·
                    have h := List.all_eq_true.mp checkChunk266_pass (i-34048)
                      (List.mem_range.mpr (by omega))
                    have heq : 34048+(i-34048) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (34048+(i-34048)))
    ·
      by_cases h2 : i < 39936
      ·
        by_cases h3 : i < 36992
        ·
          by_cases h4 : i < 35584
          ·
            by_cases h5 : i < 34816
            ·
              by_cases h6 : i < 34432
              ·
                by_cases h7 : i < 34304
                ·
                  have h := List.all_eq_true.mp checkChunk267_pass (i-34176)
                    (List.mem_range.mpr (by omega))
                  have heq : 34176+(i-34176) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (34176+(i-34176)))
                ·
                  have h := List.all_eq_true.mp checkChunk268_pass (i-34304)
                    (List.mem_range.mpr (by omega))
                  have heq : 34304+(i-34304) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (34304+(i-34304)))
              ·
                by_cases h7 : i < 34560
                ·
                  have h := List.all_eq_true.mp checkChunk269_pass (i-34432)
                    (List.mem_range.mpr (by omega))
                  have heq : 34432+(i-34432) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (34432+(i-34432)))
                ·
                  by_cases h8 : i < 34688
                  ·
                    have h := List.all_eq_true.mp checkChunk270_pass (i-34560)
                      (List.mem_range.mpr (by omega))
                    have heq : 34560+(i-34560) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (34560+(i-34560)))
                  ·
                    have h := List.all_eq_true.mp checkChunk271_pass (i-34688)
                      (List.mem_range.mpr (by omega))
                    have heq : 34688+(i-34688) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (34688+(i-34688)))
            ·
              by_cases h6 : i < 35200
              ·
                by_cases h7 : i < 34944
                ·
                  have h := List.all_eq_true.mp checkChunk272_pass (i-34816)
                    (List.mem_range.mpr (by omega))
                  have heq : 34816+(i-34816) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (34816+(i-34816)))
                ·
                  by_cases h8 : i < 35072
                  ·
                    have h := List.all_eq_true.mp checkChunk273_pass (i-34944)
                      (List.mem_range.mpr (by omega))
                    have heq : 34944+(i-34944) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (34944+(i-34944)))
                  ·
                    have h := List.all_eq_true.mp checkChunk274_pass (i-35072)
                      (List.mem_range.mpr (by omega))
                    have heq : 35072+(i-35072) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (35072+(i-35072)))
              ·
                by_cases h7 : i < 35328
                ·
                  have h := List.all_eq_true.mp checkChunk275_pass (i-35200)
                    (List.mem_range.mpr (by omega))
                  have heq : 35200+(i-35200) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (35200+(i-35200)))
                ·
                  by_cases h8 : i < 35456
                  ·
                    have h := List.all_eq_true.mp checkChunk276_pass (i-35328)
                      (List.mem_range.mpr (by omega))
                    have heq : 35328+(i-35328) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (35328+(i-35328)))
                  ·
                    have h := List.all_eq_true.mp checkChunk277_pass (i-35456)
                      (List.mem_range.mpr (by omega))
                    have heq : 35456+(i-35456) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (35456+(i-35456)))
          ·
            by_cases h5 : i < 36224
            ·
              by_cases h6 : i < 35840
              ·
                by_cases h7 : i < 35712
                ·
                  have h := List.all_eq_true.mp checkChunk278_pass (i-35584)
                    (List.mem_range.mpr (by omega))
                  have heq : 35584+(i-35584) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (35584+(i-35584)))
                ·
                  have h := List.all_eq_true.mp checkChunk279_pass (i-35712)
                    (List.mem_range.mpr (by omega))
                  have heq : 35712+(i-35712) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (35712+(i-35712)))
              ·
                by_cases h7 : i < 35968
                ·
                  have h := List.all_eq_true.mp checkChunk280_pass (i-35840)
                    (List.mem_range.mpr (by omega))
                  have heq : 35840+(i-35840) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (35840+(i-35840)))
                ·
                  by_cases h8 : i < 36096
                  ·
                    have h := List.all_eq_true.mp checkChunk281_pass (i-35968)
                      (List.mem_range.mpr (by omega))
                    have heq : 35968+(i-35968) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (35968+(i-35968)))
                  ·
                    have h := List.all_eq_true.mp checkChunk282_pass (i-36096)
                      (List.mem_range.mpr (by omega))
                    have heq : 36096+(i-36096) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (36096+(i-36096)))
            ·
              by_cases h6 : i < 36608
              ·
                by_cases h7 : i < 36352
                ·
                  have h := List.all_eq_true.mp checkChunk283_pass (i-36224)
                    (List.mem_range.mpr (by omega))
                  have heq : 36224+(i-36224) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (36224+(i-36224)))
                ·
                  by_cases h8 : i < 36480
                  ·
                    have h := List.all_eq_true.mp checkChunk284_pass (i-36352)
                      (List.mem_range.mpr (by omega))
                    have heq : 36352+(i-36352) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (36352+(i-36352)))
                  ·
                    have h := List.all_eq_true.mp checkChunk285_pass (i-36480)
                      (List.mem_range.mpr (by omega))
                    have heq : 36480+(i-36480) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (36480+(i-36480)))
              ·
                by_cases h7 : i < 36736
                ·
                  have h := List.all_eq_true.mp checkChunk286_pass (i-36608)
                    (List.mem_range.mpr (by omega))
                  have heq : 36608+(i-36608) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (36608+(i-36608)))
                ·
                  by_cases h8 : i < 36864
                  ·
                    have h := List.all_eq_true.mp checkChunk287_pass (i-36736)
                      (List.mem_range.mpr (by omega))
                    have heq : 36736+(i-36736) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (36736+(i-36736)))
                  ·
                    have h := List.all_eq_true.mp checkChunk288_pass (i-36864)
                      (List.mem_range.mpr (by omega))
                    have heq : 36864+(i-36864) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (36864+(i-36864)))
        ·
          by_cases h4 : i < 38400
          ·
            by_cases h5 : i < 37632
            ·
              by_cases h6 : i < 37248
              ·
                by_cases h7 : i < 37120
                ·
                  have h := List.all_eq_true.mp checkChunk289_pass (i-36992)
                    (List.mem_range.mpr (by omega))
                  have heq : 36992+(i-36992) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (36992+(i-36992)))
                ·
                  have h := List.all_eq_true.mp checkChunk290_pass (i-37120)
                    (List.mem_range.mpr (by omega))
                  have heq : 37120+(i-37120) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (37120+(i-37120)))
              ·
                by_cases h7 : i < 37376
                ·
                  have h := List.all_eq_true.mp checkChunk291_pass (i-37248)
                    (List.mem_range.mpr (by omega))
                  have heq : 37248+(i-37248) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (37248+(i-37248)))
                ·
                  by_cases h8 : i < 37504
                  ·
                    have h := List.all_eq_true.mp checkChunk292_pass (i-37376)
                      (List.mem_range.mpr (by omega))
                    have heq : 37376+(i-37376) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (37376+(i-37376)))
                  ·
                    have h := List.all_eq_true.mp checkChunk293_pass (i-37504)
                      (List.mem_range.mpr (by omega))
                    have heq : 37504+(i-37504) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (37504+(i-37504)))
            ·
              by_cases h6 : i < 38016
              ·
                by_cases h7 : i < 37760
                ·
                  have h := List.all_eq_true.mp checkChunk294_pass (i-37632)
                    (List.mem_range.mpr (by omega))
                  have heq : 37632+(i-37632) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (37632+(i-37632)))
                ·
                  by_cases h8 : i < 37888
                  ·
                    have h := List.all_eq_true.mp checkChunk295_pass (i-37760)
                      (List.mem_range.mpr (by omega))
                    have heq : 37760+(i-37760) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (37760+(i-37760)))
                  ·
                    have h := List.all_eq_true.mp checkChunk296_pass (i-37888)
                      (List.mem_range.mpr (by omega))
                    have heq : 37888+(i-37888) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (37888+(i-37888)))
              ·
                by_cases h7 : i < 38144
                ·
                  have h := List.all_eq_true.mp checkChunk297_pass (i-38016)
                    (List.mem_range.mpr (by omega))
                  have heq : 38016+(i-38016) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (38016+(i-38016)))
                ·
                  by_cases h8 : i < 38272
                  ·
                    have h := List.all_eq_true.mp checkChunk298_pass (i-38144)
                      (List.mem_range.mpr (by omega))
                    have heq : 38144+(i-38144) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (38144+(i-38144)))
                  ·
                    have h := List.all_eq_true.mp checkChunk299_pass (i-38272)
                      (List.mem_range.mpr (by omega))
                    have heq : 38272+(i-38272) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (38272+(i-38272)))
          ·
            by_cases h5 : i < 39168
            ·
              by_cases h6 : i < 38784
              ·
                by_cases h7 : i < 38528
                ·
                  have h := List.all_eq_true.mp checkChunk300_pass (i-38400)
                    (List.mem_range.mpr (by omega))
                  have heq : 38400+(i-38400) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (38400+(i-38400)))
                ·
                  by_cases h8 : i < 38656
                  ·
                    have h := List.all_eq_true.mp checkChunk301_pass (i-38528)
                      (List.mem_range.mpr (by omega))
                    have heq : 38528+(i-38528) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (38528+(i-38528)))
                  ·
                    have h := List.all_eq_true.mp checkChunk302_pass (i-38656)
                      (List.mem_range.mpr (by omega))
                    have heq : 38656+(i-38656) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (38656+(i-38656)))
              ·
                by_cases h7 : i < 38912
                ·
                  have h := List.all_eq_true.mp checkChunk303_pass (i-38784)
                    (List.mem_range.mpr (by omega))
                  have heq : 38784+(i-38784) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (38784+(i-38784)))
                ·
                  by_cases h8 : i < 39040
                  ·
                    have h := List.all_eq_true.mp checkChunk304_pass (i-38912)
                      (List.mem_range.mpr (by omega))
                    have heq : 38912+(i-38912) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (38912+(i-38912)))
                  ·
                    have h := List.all_eq_true.mp checkChunk305_pass (i-39040)
                      (List.mem_range.mpr (by omega))
                    have heq : 39040+(i-39040) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (39040+(i-39040)))
            ·
              by_cases h6 : i < 39552
              ·
                by_cases h7 : i < 39296
                ·
                  have h := List.all_eq_true.mp checkChunk306_pass (i-39168)
                    (List.mem_range.mpr (by omega))
                  have heq : 39168+(i-39168) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (39168+(i-39168)))
                ·
                  by_cases h8 : i < 39424
                  ·
                    have h := List.all_eq_true.mp checkChunk307_pass (i-39296)
                      (List.mem_range.mpr (by omega))
                    have heq : 39296+(i-39296) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (39296+(i-39296)))
                  ·
                    have h := List.all_eq_true.mp checkChunk308_pass (i-39424)
                      (List.mem_range.mpr (by omega))
                    have heq : 39424+(i-39424) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (39424+(i-39424)))
              ·
                by_cases h7 : i < 39680
                ·
                  have h := List.all_eq_true.mp checkChunk309_pass (i-39552)
                    (List.mem_range.mpr (by omega))
                  have heq : 39552+(i-39552) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (39552+(i-39552)))
                ·
                  by_cases h8 : i < 39808
                  ·
                    have h := List.all_eq_true.mp checkChunk310_pass (i-39680)
                      (List.mem_range.mpr (by omega))
                    have heq : 39680+(i-39680) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (39680+(i-39680)))
                  ·
                    have h := List.all_eq_true.mp checkChunk311_pass (i-39808)
                      (List.mem_range.mpr (by omega))
                    have heq : 39808+(i-39808) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (39808+(i-39808)))
      ·
        by_cases h3 : i < 42752
        ·
          by_cases h4 : i < 41344
          ·
            by_cases h5 : i < 40576
            ·
              by_cases h6 : i < 40192
              ·
                by_cases h7 : i < 40064
                ·
                  have h := List.all_eq_true.mp checkChunk312_pass (i-39936)
                    (List.mem_range.mpr (by omega))
                  have heq : 39936+(i-39936) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (39936+(i-39936)))
                ·
                  have h := List.all_eq_true.mp checkChunk313_pass (i-40064)
                    (List.mem_range.mpr (by omega))
                  have heq : 40064+(i-40064) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (40064+(i-40064)))
              ·
                by_cases h7 : i < 40320
                ·
                  have h := List.all_eq_true.mp checkChunk314_pass (i-40192)
                    (List.mem_range.mpr (by omega))
                  have heq : 40192+(i-40192) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (40192+(i-40192)))
                ·
                  by_cases h8 : i < 40448
                  ·
                    have h := List.all_eq_true.mp checkChunk315_pass (i-40320)
                      (List.mem_range.mpr (by omega))
                    have heq : 40320+(i-40320) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (40320+(i-40320)))
                  ·
                    have h := List.all_eq_true.mp checkChunk316_pass (i-40448)
                      (List.mem_range.mpr (by omega))
                    have heq : 40448+(i-40448) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (40448+(i-40448)))
            ·
              by_cases h6 : i < 40960
              ·
                by_cases h7 : i < 40704
                ·
                  have h := List.all_eq_true.mp checkChunk317_pass (i-40576)
                    (List.mem_range.mpr (by omega))
                  have heq : 40576+(i-40576) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (40576+(i-40576)))
                ·
                  by_cases h8 : i < 40832
                  ·
                    have h := List.all_eq_true.mp checkChunk318_pass (i-40704)
                      (List.mem_range.mpr (by omega))
                    have heq : 40704+(i-40704) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (40704+(i-40704)))
                  ·
                    have h := List.all_eq_true.mp checkChunk319_pass (i-40832)
                      (List.mem_range.mpr (by omega))
                    have heq : 40832+(i-40832) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (40832+(i-40832)))
              ·
                by_cases h7 : i < 41088
                ·
                  have h := List.all_eq_true.mp checkChunk320_pass (i-40960)
                    (List.mem_range.mpr (by omega))
                  have heq : 40960+(i-40960) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (40960+(i-40960)))
                ·
                  by_cases h8 : i < 41216
                  ·
                    have h := List.all_eq_true.mp checkChunk321_pass (i-41088)
                      (List.mem_range.mpr (by omega))
                    have heq : 41088+(i-41088) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (41088+(i-41088)))
                  ·
                    have h := List.all_eq_true.mp checkChunk322_pass (i-41216)
                      (List.mem_range.mpr (by omega))
                    have heq : 41216+(i-41216) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (41216+(i-41216)))
          ·
            by_cases h5 : i < 41984
            ·
              by_cases h6 : i < 41600
              ·
                by_cases h7 : i < 41472
                ·
                  have h := List.all_eq_true.mp checkChunk323_pass (i-41344)
                    (List.mem_range.mpr (by omega))
                  have heq : 41344+(i-41344) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (41344+(i-41344)))
                ·
                  have h := List.all_eq_true.mp checkChunk324_pass (i-41472)
                    (List.mem_range.mpr (by omega))
                  have heq : 41472+(i-41472) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (41472+(i-41472)))
              ·
                by_cases h7 : i < 41728
                ·
                  have h := List.all_eq_true.mp checkChunk325_pass (i-41600)
                    (List.mem_range.mpr (by omega))
                  have heq : 41600+(i-41600) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (41600+(i-41600)))
                ·
                  by_cases h8 : i < 41856
                  ·
                    have h := List.all_eq_true.mp checkChunk326_pass (i-41728)
                      (List.mem_range.mpr (by omega))
                    have heq : 41728+(i-41728) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (41728+(i-41728)))
                  ·
                    have h := List.all_eq_true.mp checkChunk327_pass (i-41856)
                      (List.mem_range.mpr (by omega))
                    have heq : 41856+(i-41856) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (41856+(i-41856)))
            ·
              by_cases h6 : i < 42368
              ·
                by_cases h7 : i < 42112
                ·
                  have h := List.all_eq_true.mp checkChunk328_pass (i-41984)
                    (List.mem_range.mpr (by omega))
                  have heq : 41984+(i-41984) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (41984+(i-41984)))
                ·
                  by_cases h8 : i < 42240
                  ·
                    have h := List.all_eq_true.mp checkChunk329_pass (i-42112)
                      (List.mem_range.mpr (by omega))
                    have heq : 42112+(i-42112) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (42112+(i-42112)))
                  ·
                    have h := List.all_eq_true.mp checkChunk330_pass (i-42240)
                      (List.mem_range.mpr (by omega))
                    have heq : 42240+(i-42240) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (42240+(i-42240)))
              ·
                by_cases h7 : i < 42496
                ·
                  have h := List.all_eq_true.mp checkChunk331_pass (i-42368)
                    (List.mem_range.mpr (by omega))
                  have heq : 42368+(i-42368) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (42368+(i-42368)))
                ·
                  by_cases h8 : i < 42624
                  ·
                    have h := List.all_eq_true.mp checkChunk332_pass (i-42496)
                      (List.mem_range.mpr (by omega))
                    have heq : 42496+(i-42496) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (42496+(i-42496)))
                  ·
                    have h := List.all_eq_true.mp checkChunk333_pass (i-42624)
                      (List.mem_range.mpr (by omega))
                    have heq : 42624+(i-42624) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (42624+(i-42624)))
        ·
          by_cases h4 : i < 44160
          ·
            by_cases h5 : i < 43392
            ·
              by_cases h6 : i < 43008
              ·
                by_cases h7 : i < 42880
                ·
                  have h := List.all_eq_true.mp checkChunk334_pass (i-42752)
                    (List.mem_range.mpr (by omega))
                  have heq : 42752+(i-42752) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (42752+(i-42752)))
                ·
                  have h := List.all_eq_true.mp checkChunk335_pass (i-42880)
                    (List.mem_range.mpr (by omega))
                  have heq : 42880+(i-42880) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (42880+(i-42880)))
              ·
                by_cases h7 : i < 43136
                ·
                  have h := List.all_eq_true.mp checkChunk336_pass (i-43008)
                    (List.mem_range.mpr (by omega))
                  have heq : 43008+(i-43008) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (43008+(i-43008)))
                ·
                  by_cases h8 : i < 43264
                  ·
                    have h := List.all_eq_true.mp checkChunk337_pass (i-43136)
                      (List.mem_range.mpr (by omega))
                    have heq : 43136+(i-43136) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (43136+(i-43136)))
                  ·
                    have h := List.all_eq_true.mp checkChunk338_pass (i-43264)
                      (List.mem_range.mpr (by omega))
                    have heq : 43264+(i-43264) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (43264+(i-43264)))
            ·
              by_cases h6 : i < 43776
              ·
                by_cases h7 : i < 43520
                ·
                  have h := List.all_eq_true.mp checkChunk339_pass (i-43392)
                    (List.mem_range.mpr (by omega))
                  have heq : 43392+(i-43392) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (43392+(i-43392)))
                ·
                  by_cases h8 : i < 43648
                  ·
                    have h := List.all_eq_true.mp checkChunk340_pass (i-43520)
                      (List.mem_range.mpr (by omega))
                    have heq : 43520+(i-43520) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (43520+(i-43520)))
                  ·
                    have h := List.all_eq_true.mp checkChunk341_pass (i-43648)
                      (List.mem_range.mpr (by omega))
                    have heq : 43648+(i-43648) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (43648+(i-43648)))
              ·
                by_cases h7 : i < 43904
                ·
                  have h := List.all_eq_true.mp checkChunk342_pass (i-43776)
                    (List.mem_range.mpr (by omega))
                  have heq : 43776+(i-43776) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (43776+(i-43776)))
                ·
                  by_cases h8 : i < 44032
                  ·
                    have h := List.all_eq_true.mp checkChunk343_pass (i-43904)
                      (List.mem_range.mpr (by omega))
                    have heq : 43904+(i-43904) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (43904+(i-43904)))
                  ·
                    have h := List.all_eq_true.mp checkChunk344_pass (i-44032)
                      (List.mem_range.mpr (by omega))
                    have heq : 44032+(i-44032) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (44032+(i-44032)))
          ·
            by_cases h5 : i < 44928
            ·
              by_cases h6 : i < 44544
              ·
                by_cases h7 : i < 44288
                ·
                  have h := List.all_eq_true.mp checkChunk345_pass (i-44160)
                    (List.mem_range.mpr (by omega))
                  have heq : 44160+(i-44160) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (44160+(i-44160)))
                ·
                  by_cases h8 : i < 44416
                  ·
                    have h := List.all_eq_true.mp checkChunk346_pass (i-44288)
                      (List.mem_range.mpr (by omega))
                    have heq : 44288+(i-44288) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (44288+(i-44288)))
                  ·
                    have h := List.all_eq_true.mp checkChunk347_pass (i-44416)
                      (List.mem_range.mpr (by omega))
                    have heq : 44416+(i-44416) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (44416+(i-44416)))
              ·
                by_cases h7 : i < 44672
                ·
                  have h := List.all_eq_true.mp checkChunk348_pass (i-44544)
                    (List.mem_range.mpr (by omega))
                  have heq : 44544+(i-44544) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (44544+(i-44544)))
                ·
                  by_cases h8 : i < 44800
                  ·
                    have h := List.all_eq_true.mp checkChunk349_pass (i-44672)
                      (List.mem_range.mpr (by omega))
                    have heq : 44672+(i-44672) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (44672+(i-44672)))
                  ·
                    have h := List.all_eq_true.mp checkChunk350_pass (i-44800)
                      (List.mem_range.mpr (by omega))
                    have heq : 44800+(i-44800) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (44800+(i-44800)))
            ·
              by_cases h6 : i < 45312
              ·
                by_cases h7 : i < 45056
                ·
                  have h := List.all_eq_true.mp checkChunk351_pass (i-44928)
                    (List.mem_range.mpr (by omega))
                  have heq : 44928+(i-44928) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (44928+(i-44928)))
                ·
                  by_cases h8 : i < 45184
                  ·
                    have h := List.all_eq_true.mp checkChunk352_pass (i-45056)
                      (List.mem_range.mpr (by omega))
                    have heq : 45056+(i-45056) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (45056+(i-45056)))
                  ·
                    have h := List.all_eq_true.mp checkChunk353_pass (i-45184)
                      (List.mem_range.mpr (by omega))
                    have heq : 45184+(i-45184) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (45184+(i-45184)))
              ·
                by_cases h7 : i < 45440
                ·
                  have h := List.all_eq_true.mp checkChunk354_pass (i-45312)
                    (List.mem_range.mpr (by omega))
                  have heq : 45312+(i-45312) = i := by omega
                  simpa only [heq] using (of_decide_eq_true h :
                    Node.Check scale inputs nodes (45312+(i-45312)))
                ·
                  by_cases h8 : i < 45568
                  ·
                    have h := List.all_eq_true.mp checkChunk355_pass (i-45440)
                      (List.mem_range.mpr (by omega))
                    have heq : 45440+(i-45440) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (45440+(i-45440)))
                  ·
                    have h := List.all_eq_true.mp checkChunk356_pass (i-45568)
                      (List.mem_range.mpr (by omega))
                    have heq : 45568+(i-45568) = i := by omega
                    simpa only [heq] using (of_decide_eq_true h :
                      Node.Check scale inputs nodes (45568+(i-45568)))
theorem all_enclosures (values : ℕ → ℝ)
    (hvalues : ∀ i, ScaledInterval.Contains scale (inputs i) (values i)) :
    ∀ i, i < 45592 → ScaledInterval.Contains scale (nodes i).bound
      (IntervalCircuit.value values nodes i) :=
  checks_sound (by decide) inputs values nodes 45592 hvalues node_checks
#print axioms node_checks
#print axioms all_enclosures
end ThomsonN10.Local.Certificates.AmbientKernel
