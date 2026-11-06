import Mathlib

theorem number_theory_246917 :
    {x : ℤ | ∃ m n l : ℤ, x = 12 * m + 8 * n + 4 * l} =
    {x : ℤ | ∃ p q r : ℤ, x = 20 * p + 16 * q + 12 * r} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume x ∈ M, prove x ∈ N
    rintro ⟨m, n, l, hx⟩
    use -3 * (2 * n + l)
    use 4 * (2 * n + l)
    use m
    linarith
  · -- Assume x ∈ N, prove x ∈ M
    rintro ⟨p, q, r, hx⟩
    use p
    use p + 2 * q + r
    use r
    linarith