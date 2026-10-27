theorem kernel_equality (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    RingHom.ker (phi p) = minorIdeal p
