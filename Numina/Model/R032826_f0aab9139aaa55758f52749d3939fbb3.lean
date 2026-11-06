import Mathlib

theorem number_theory_10498 :
    {x : ℤ | ∃ m n l, x = 12 * m + 8 * n + 4 * l} =
    {x : ℤ | ∃ p q r, x = 20 * p + 16 * q + 12 * r} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- First, prove {x : ℤ | ∃ m n l, x = 12 * m + 8 * n + 4 * l} ⊆ {x : ℤ | ∃ p q r, x = 20 * p + 16 * q + 12 * r}
    rintro ⟨m, n, l, hx⟩
    have h1 : x = 4 * (3 * m + 2 * n + l) := by linarith
    use (3 * m + 2 * n + l), (- (3 * m + 2 * n + l) : ℤ), (0 : ℤ)
    linarith [h1]
  · -- Now, prove the reverse direction {x : ℤ | ∃ p q r, x = 20 * p + 16 * q + 12 * r} ⊆ {x : ℤ | ∃ m n l, x = 12 * m + 8 * n + 4 * l}
    rintro ⟨p, q, r, hx⟩
    have h1 : x = 4 * (5 * p + 4 * q + 3 * r) := by linarith
    use p, p + 2 * q + r, r
    linarith [h1]