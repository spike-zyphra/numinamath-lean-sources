import Mathlib

theorem number_theory_192625 :
    {x : ℤ | ∃ m n l : ℤ, x = 12 * m + 8 * n + 4 * l} =
    {x : ℤ | ∃ p q r : ℤ, x = 20 * p + 16 * q + 12 * r} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume x ∈ LHS, prove RHS
    rintro ⟨m, n, l, hx⟩
    use (3 * m + 2 * n + l)
    use -(3 * m + 2 * n + l)
    use 0
    linarith
  · -- Assume x ∈ RHS, prove LHS
    rintro ⟨p, q, r, hx⟩
    use (5 * p + 4 * q + 3 * r)
    use -(5 * p + 4 * q + 3 * r)
    use 0
    linarith