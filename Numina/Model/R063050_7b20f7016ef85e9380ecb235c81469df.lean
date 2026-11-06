import Mathlib

theorem number_theory_284766 :
    {u : ℤ | ∃ m n l, u = 12 * m + 8 * n + 4 * l} =
    {u : ℤ | ∃ p q r, u = 20 * p + 16 * q + 12 * r} := by
  ext u
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Forward direction: {u : ℤ | ∃ m n l, u = 12 * m + 8 * n + 4 * l} ⊆ {u : ℤ | ∃ p q r, u = 20 * p + 16 * q + 12 * r}
    rintro ⟨m, n, l, h⟩
    use (3 * m + 2 * n + l), (- (3 * m + 2 * n + l)), 0
    linarith
  · -- Reverse direction: {u : ℤ | ∃ p q r, u = 20 * p + 16 * q + 12 * r} ⊆ {u : ℤ | ∃ m n l, u = 12 * m + 8 * n + 4 * l}
    rintro ⟨p, q, r, h⟩
    use 0, 0, 5 * p + 4 * q + 3 * r
    linarith