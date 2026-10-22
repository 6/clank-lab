import Mathlib
import OAI.NumberTheory.Ostmann.Arithmetic.ResidueIntervals

namespace OAI

/-! # Natural residue representatives and the Haar unit averages used by CRT -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def unitReducedResidueEquiv (q : ℕ) [NeZero q] :
    (ZMod q)ˣ ≃ {a : ℕ // a ∈ reducedResidues q} where
  toFun u := ⟨(u : ZMod q).val, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime u⟩⟩
  invFun a := ZMod.unitOfCoprime a.val (Finset.mem_filter.mp a.property).2
  left_inv u := Units.ext (ZMod.natCast_zmod_val _)
  right_inv a := by
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp a.property).1)

end Ostmann

end OAI
