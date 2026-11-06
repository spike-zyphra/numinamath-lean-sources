import Mathlib

theorem number_theory_155330 :
    {x : ℤ | ∃ m n l, x = 12 * m + 8 * n + 4 * l} =
    {x : ℤ | ∃ p q r, x = 20 * p + 16 * q + 12 * r} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume x ∈ {x : ℤ | ∃ m n l, x = 12 * m + 8 * n + 4 * l}, prove x ∈ {x : ℤ | ∃ p q r, x = 20 * p + 16 * q + 12 * r}
    rintro ⟨m, n, l, hx⟩
    use 1
    use 3 * m + 2 * n + l - 5
    use 5 - (3 * m + 2 * n + l)
    linarith [hx]
  · -- Assume x ∈ {x : ℤ | ∃ p q r, x = 20 * p + 16 * q + 12 * r}, prove x ∈ {x : ℤ | ∃ m n l, x = 12 * m + 8 * n + 4 * l}
    rintro ⟨p, q, r, hx⟩
    use 0
    use 0
    use 5 * p + 4 * q + 3 * r
    linarith [hx]