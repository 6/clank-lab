import LocalRup.SymmetryFree.Chunk00
import LocalRup.SymmetryFree.Chunk01
import LocalRup.SymmetryFree.Chunk02
import LocalRup.SymmetryFree.Chunk03
import LocalRup.SymmetryFree.Chunk04
import LocalRup.SymmetryFree.Chunk05
import LocalRup.SymmetryFree.Chunk06
import LocalRup.SymmetryFree.Chunk07
import LocalRup.SymmetryFree.Chunk08
import LocalRup.SymmetryFree.Chunk09
import LocalRup.SymmetryFree.Chunk10
import LocalRup.SymmetryFree.Chunk11
import LocalRup.SymmetryFree.Chunk12
import LocalRup.SymmetryFree.Chunk13
import LocalRup.SymmetryFree.Chunk14
import LocalRup.SymmetryFree.Chunk15
import LocalRup.SymmetryFree.Chunk16
import LocalRup.SymmetryFree.Chunk17
import LocalRup.SymmetryFree.Chunk18
import LocalRup.SymmetryFree.Chunk19
import LocalRup.SymmetryFree.Chunk20
import LocalRup.SymmetryFree.Chunk21
import LocalRup.SymmetryFree.Chunk22
import LocalRup.SymmetryFree.Chunk23
import LocalRup.SymmetryFree.Chunk24
import LocalRup.SymmetryFree.Chunk25
import LocalRup.SymmetryFree.Chunk26
import LocalRup.SymmetryFree.Chunk27
import LocalRup.SymmetryFree.Chunk28
import LocalRup.SymmetryFree.Chunk29
import LocalRup.SymmetryFree.Chunk30
import LocalRup.SymmetryFree.Chunk31
import LocalRup.SymmetryFree.Chunk32
import LocalRup.SymmetryFree.Chunk33
import LocalRup.SymmetryFree.Chunk34
import LocalRup.SymmetryFree.Chunk35
import LocalRup.SymmetryFree.Chunk36
import LocalRup.SymmetryFree.Chunk37
import LocalRup.SymmetryFree.Chunk38

namespace LocalRup.SymmetryFree.LeanCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem full_checked : AllChecked state0 (proof) :=
  (checked_append state0 (((((chunk0 ++ chunk1) ++ (chunk2 ++ chunk3)) ++ ((chunk4 ++ chunk5) ++ (chunk6 ++ (chunk7 ++ chunk8)))) ++ (((chunk9 ++ chunk10) ++ (chunk11 ++ (chunk12 ++ chunk13))) ++ ((chunk14 ++ chunk15) ++ (chunk16 ++ (chunk17 ++ chunk18)))))) (((((chunk19 ++ chunk20) ++ (chunk21 ++ (chunk22 ++ chunk23))) ++ ((chunk24 ++ chunk25) ++ (chunk26 ++ (chunk27 ++ chunk28)))) ++ (((chunk29 ++ chunk30) ++ (chunk31 ++ (chunk32 ++ chunk33))) ++ ((chunk34 ++ chunk35) ++ (chunk36 ++ (chunk37 ++ chunk38)))))) (checked_append state0 ((((chunk0 ++ chunk1) ++ (chunk2 ++ chunk3)) ++ ((chunk4 ++ chunk5) ++ (chunk6 ++ (chunk7 ++ chunk8))))) ((((chunk9 ++ chunk10) ++ (chunk11 ++ (chunk12 ++ chunk13))) ++ ((chunk14 ++ chunk15) ++ (chunk16 ++ (chunk17 ++ chunk18))))) (checked_append state0 (((chunk0 ++ chunk1) ++ (chunk2 ++ chunk3))) (((chunk4 ++ chunk5) ++ (chunk6 ++ (chunk7 ++ chunk8)))) (checked_append state0 ((chunk0 ++ chunk1)) ((chunk2 ++ chunk3)) (checked_append state0 (chunk0) (chunk1) chunk0_checked chunk1_checked) (checked_append state14 (chunk2) (chunk3) chunk2_checked chunk3_checked)) (checked_append state28 ((chunk4 ++ chunk5)) ((chunk6 ++ (chunk7 ++ chunk8))) (checked_append state28 (chunk4) (chunk5) chunk4_checked chunk5_checked) (checked_append state45 (chunk6) ((chunk7 ++ chunk8)) chunk6_checked (checked_append state52 (chunk7) (chunk8) chunk7_checked chunk8_checked)))) (checked_append state69 (((chunk9 ++ chunk10) ++ (chunk11 ++ (chunk12 ++ chunk13)))) (((chunk14 ++ chunk15) ++ (chunk16 ++ (chunk17 ++ chunk18)))) (checked_append state69 ((chunk9 ++ chunk10)) ((chunk11 ++ (chunk12 ++ chunk13))) (checked_append state69 (chunk9) (chunk10) chunk9_checked chunk10_checked) (checked_append state88 (chunk11) ((chunk12 ++ chunk13)) chunk11_checked (checked_append state98 (chunk12) (chunk13) chunk12_checked chunk13_checked))) (checked_append state118 ((chunk14 ++ chunk15)) ((chunk16 ++ (chunk17 ++ chunk18))) (checked_append state118 (chunk14) (chunk15) chunk14_checked chunk15_checked) (checked_append state134 (chunk16) ((chunk17 ++ chunk18)) chunk16_checked (checked_append state142 (chunk17) (chunk18) chunk17_checked chunk18_checked))))) (checked_append state161 ((((chunk19 ++ chunk20) ++ (chunk21 ++ (chunk22 ++ chunk23))) ++ ((chunk24 ++ chunk25) ++ (chunk26 ++ (chunk27 ++ chunk28))))) ((((chunk29 ++ chunk30) ++ (chunk31 ++ (chunk32 ++ chunk33))) ++ ((chunk34 ++ chunk35) ++ (chunk36 ++ (chunk37 ++ chunk38))))) (checked_append state161 (((chunk19 ++ chunk20) ++ (chunk21 ++ (chunk22 ++ chunk23)))) (((chunk24 ++ chunk25) ++ (chunk26 ++ (chunk27 ++ chunk28)))) (checked_append state161 ((chunk19 ++ chunk20)) ((chunk21 ++ (chunk22 ++ chunk23))) (checked_append state161 (chunk19) (chunk20) chunk19_checked chunk20_checked) (checked_append state180 (chunk21) ((chunk22 ++ chunk23)) chunk21_checked (checked_append state190 (chunk22) (chunk23) chunk22_checked chunk23_checked))) (checked_append state205 ((chunk24 ++ chunk25)) ((chunk26 ++ (chunk27 ++ chunk28))) (checked_append state205 (chunk24) (chunk25) chunk24_checked chunk25_checked) (checked_append state224 (chunk26) ((chunk27 ++ chunk28)) chunk26_checked (checked_append state233 (chunk27) (chunk28) chunk27_checked chunk28_checked)))) (checked_append state251 (((chunk29 ++ chunk30) ++ (chunk31 ++ (chunk32 ++ chunk33)))) (((chunk34 ++ chunk35) ++ (chunk36 ++ (chunk37 ++ chunk38)))) (checked_append state251 ((chunk29 ++ chunk30)) ((chunk31 ++ (chunk32 ++ chunk33))) (checked_append state251 (chunk29) (chunk30) chunk29_checked chunk30_checked) (checked_append state269 (chunk31) ((chunk32 ++ chunk33)) chunk31_checked (checked_append state279 (chunk32) (chunk33) chunk32_checked chunk33_checked))) (checked_append state298 ((chunk34 ++ chunk35)) ((chunk36 ++ (chunk37 ++ chunk38))) (checked_append state298 (chunk34) (chunk35) chunk34_checked chunk35_checked) (checked_append state317 (chunk36) ((chunk37 ++ chunk38)) chunk36_checked (checked_append state327 (chunk37) (chunk38) chunk37_checked chunk38_checked))))))

theorem certificate_true : checkFrom (initial input) proof = true := by
  simp only [checkFrom, Bool.and_eq_true]
  exact ⟨by decide +kernel, (runChecks_eq _ _).mpr full_checked⟩

theorem raw_unsat : Unsat input :=
  checkFrom_sound input (initial input) proof (initial_good input) certificate_true

theorem cnf_unsat : cnf.Unsat := toStd_unsat input raw_unsat

/-- info: 'LocalRup.SymmetryFree.LeanCertificate.raw_unsat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_unsat

/-- info: 'LocalRup.SymmetryFree.LeanCertificate.cnf_unsat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cnf_unsat

end LocalRup.SymmetryFree.LeanCertificate
