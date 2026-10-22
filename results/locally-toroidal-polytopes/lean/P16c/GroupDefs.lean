import P16c.Generators

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]

def tGen (a b : K) (ha : a ≠ 0) : (Mat K)ˣ :=
  generators a b ha 0 * generators a b ha 1 * generators a b ha 2 * generators a b ha 1
def vGen (a b : K) (ha : a ≠ 0) : (Mat K)ˣ :=
  generators a b ha 1 * generators a b ha 2 * generators a b ha 3 * generators a b ha 2
def t₂Gen (a b : K) (ha : a ≠ 0) : (Mat K)ˣ :=
  generators a b ha 1 * tGen a b ha * generators a b ha 1
def v₂Gen (a b : K) (ha : a ≠ 0) : (Mat K)ˣ :=
  generators a b ha 2 * vGen a b ha * generators a b ha 2

@[simp] lemma val_tGen (a b : K) (ha : a ≠ 0) : ↑(tGen a b ha) = T a b := rfl
@[simp] lemma val_vGen (a b : K) (ha : a ≠ 0) : ↑(vGen a b ha) = V a b := rfl
@[simp] lemma val_t₂Gen (a b : K) (ha : a ≠ 0) : ↑(t₂Gen a b ha) = T₂ a b := rfl
@[simp] lemma val_v₂Gen (a b : K) (ha : a ≠ 0) : ↑(v₂Gen a b ha) = V₂ a b := rfl

def AF (a b : K) (ha : a ≠ 0) : Subgroup (Mat K)ˣ := Subgroup.closure {tGen a b ha, t₂Gen a b ha}
def AV (a b : K) (ha : a ≠ 0) : Subgroup (Mat K)ˣ := Subgroup.closure {vGen a b ha, v₂Gen a b ha}
def D (a b : K) (ha : a ≠ 0) : Subgroup (Mat K)ˣ := Subgroup.closure {generators a b ha 1, generators a b ha 2}
def F (a b : K) (ha : a ≠ 0) : Subgroup (Mat K)ˣ := Subgroup.closure {generators a b ha 0, generators a b ha 1, generators a b ha 2}
def Ve (a b : K) (ha : a ≠ 0) : Subgroup (Mat K)ˣ := Subgroup.closure {generators a b ha 1, generators a b ha 2, generators a b ha 3}
end P16c
