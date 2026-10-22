import P16c.Normalizers
import P16c.TranslationCard
import P16c.PairRepresentation
import P16c.Commutant

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]

/-- L5's translation-group intersection, without any coprimality assumption. -/
theorem translation_intersection (a b l : K) (ha : a ≠ 0) (hl : l ≠ 0)
    (hl2 : l ^ 2 ≠ 1) (hs : Odd (orderOf l)) (hσ : a + b = traceParam l) :
    Disjoint (AF a b ha) (AV a b ha) := by
  let t := tGen a b ha
  let t₂ := t₂Gen a b ha
  let v := vGen a b ha
  let q₁ := generators a b ha 1
  let q₂ := generators a b ha 2
  have hq₁ : q₁ * q₁ = 1 := generators_involutive a b ha 1
  have hq₂ : q₂ * q₂ = 1 := generators_involutive a b ha 2
  have hq₁inv : q₁⁻¹ = q₁ := inv_eq_of_mul_eq_one_right hq₁
  have hq₂inv : q₂⁻¹ = q₂ := inv_eq_of_mul_eq_one_right hq₂
  have ht : orderOf t = orderOf l := by
    rw [← orderOf_units]
    simpa [t] using t_order a b l hl hl2 hσ
  have ht₂ : orderOf t₂ = orderOf l := by
    rw [← orderOf_units]
    simpa [t₂] using t₂_order a b l hl hl2 hσ
  have hc : Commute t t₂ := tGen_commute a b ha
  have hq₁D : q₁ ∈ D a b ha := Subgroup.subset_closure (by simp [q₁])
  have hq₂D : q₂ ∈ D a b ha := Subgroup.subset_closure (by simp [q₂])
  have hconj (q : (Mat K)ˣ) (hq : q ∈ D a b ha) {x : (Mat K)ˣ} (hx : x ∈ AV a b ha) :
      (MulAut.conj q) x ∈ AV a b ha := by
    exact (Subgroup.mem_normalizer_iff.mp (d_normalizes_av a b ha hq) x).mp hx
  have hv : v ∈ AV a b ha := Subgroup.subset_closure (by simp [v])
  have hperiod (n : ℕ) (hn : t ^ n ∈ AV a b ha) : orderOf l ∣ n := by
    haveI := av_commutative a b ha
    have hcomm : t ^ n * v = v * t ^ n := setLike_mul_comm hn hv
    apply t_power_commuting_period a b l ha hl hl2 hs hσ n
    simpa [t, v] using congrArg (fun x : (Mat K)ˣ => (x : Mat K)) hcomm
  apply Subgroup.disjoint_def.mpr
  intro x hxF hxV
  obtain ⟨i, j, hrep⟩ := commuting_pair_representation t t₂ hc
    (orderOf_pos_iff.mp (ht ▸ hs.pos)) (orderOf_pos_iff.mp (ht₂ ▸ hs.pos)) hxF
  let C := MulAut.conj q₂
  have hCt : C t = t := by simpa [C, MulAut.conj_apply, hq₂inv, t, q₂] using conjugate_t_fixed a b ha
  have hCt₂ : C t₂ = t₂⁻¹ := by simpa [C, MulAut.conj_apply, hq₂inv, t₂, q₂] using conjugate_t₂_inv a b ha
  have hCx : C x = t ^ i * (t₂⁻¹) ^ j := by rw [← hrep, map_mul, map_pow, map_pow, hCt, hCt₂]
  have hxC : C x ∈ AV a b ha := hconj q₂ hq₂D hxV
  have hfirst : x * C x = t ^ (2 * i) := by
    rw [hCx, ← hrep]
    rw [(hc.symm.pow_pow j i).mul_mul_mul_comm]
    simp only [inv_pow, mul_inv_cancel, mul_one, ← pow_add]
    congr 1
    omega
  have hsecond : x * (C x)⁻¹ = t₂ ^ (2 * j) := by
    rw [hCx, ← hrep, mul_inv_rev, inv_pow, inv_inv]
    calc
      t ^ i * t₂ ^ j * (t₂ ^ j * (t ^ i)⁻¹) =
          t ^ i * (t₂ ^ (2 * j)) * (t ^ i)⁻¹ := by rw [two_mul, pow_add]; group
      _ = t₂ ^ (2 * j) := by rw [(hc.pow_pow i (2*j)).eq]; group
  have hti : t ^ (2 * i) ∈ AV a b ha := by rw [← hfirst]; exact (AV a b ha).mul_mem hxV hxC
  have ht₂j : t₂ ^ (2 * j) ∈ AV a b ha := by
    rw [← hsecond]
    exact (AV a b ha).mul_mem hxV ((AV a b ha).inv_mem hxC)
  have htj : t ^ (2 * j) ∈ AV a b ha := by
    have hh := hconj q₁ hq₁D ht₂j
    simpa [map_pow, MulAut.conj_apply, hq₁inv, t, t₂, q₁, conjugate_t₂] using hh
  have hi : orderOf l ∣ i := hs.coprime_two_right.dvd_of_dvd_mul_left (hperiod _ hti)
  have hj : orderOf l ∣ j := hs.coprime_two_right.dvd_of_dvd_mul_left (hperiod _ htj)
  have hti1 : t ^ i = 1 := orderOf_dvd_iff_pow_eq_one.mp (ht ▸ hi)
  have htj1 : t₂ ^ j = 1 := orderOf_dvd_iff_pow_eq_one.mp (ht₂ ▸ hj)
  rw [← hrep, hti1, htj1, one_mul]
end P16c
