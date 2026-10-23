import Reduction
import IntervalCertificate

/- Endpoint type and small definition controls, checked by the default build.
   GeneralEndpoint is a specification, not an unconditional proved theorem. -/
open NoncrossingSCD

example (eligible : (W : Type) → IntervalData W → Prop)
    (coxeter : {W : Type} → IntervalData W → W → Prop) :
    GeneralEndpoint eligible coxeter ↔
      ∀ (W : Type) (D : IntervalData W), eligible W D → ∀ c, coxeter D c →
        Nonempty (SCD (Interval D c)
          (Cover (fun x y => AbsoluteLE D x.val y.val))
          (fun x => D.reflectionLength x.val) D.essentialRank) := by
  rfl

example : exceptionalNumbers.length = 26 := by decide
example : citedSmallNumbers.length = 20 := by decide
example : certificateNumbers = [30, 33, 34, 35, 36, 37] := by rfl
example : (productModels []).height = 0 := by rfl
example : (productModels []).HasSCD := finite_product_scd [] (by simp)

/-- info: 'NoncrossingSCD.productSCD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NoncrossingSCD.productSCD
/-- info: 'NoncrossingSCD.transportSCD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms NoncrossingSCD.transportSCD
/-- info: 'NoncrossingSCD.productPosetSCD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NoncrossingSCD.productPosetSCD
/-- info: 'NoncrossingSCD.intervalSCD_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms NoncrossingSCD.intervalSCD_map
/-- info: 'NoncrossingSCD.product_length_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NoncrossingSCD.product_length_spec
/-- info: 'NoncrossingSCD.reflectionLength_map' does not depend on any axioms -/
#guard_msgs in
#print axioms NoncrossingSCD.reflectionLength_map
/-- info: 'NoncrossingSCD.exceptional_table_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NoncrossingSCD.exceptional_table_split
/-- info: 'NoncrossingSCD.exceptional_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NoncrossingSCD.exceptional_reduction
/-- info: 'NoncrossingSCD.finite_product_scd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NoncrossingSCD.finite_product_scd
/-- info: 'IntervalCertificate.exact_interval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IntervalCertificate.exact_interval
/-- info: 'IntervalCertificate.certified_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IntervalCertificate.certified_rank
