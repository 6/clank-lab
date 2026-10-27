theorem kernel_equality (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    RingHom.ker (phi p) = minorIdeal p :=
  le_antisymm (ker_le_minorIdeal p hp) (minorIdeal_le_ker p)


theorem endpoint : Endpoint := kernel_equality
