import Mathlib

theorem number_theory_328396 :
    {u : ℤ | ∃ m n l : ℤ, u = 12 * m + 8 * n + 4 * l} =
    {u : ℤ | ∃ p q r : ℤ, u = 20 * p + 16 * q + 12 * r} := by 
  ext u 
  simp only [Set.mem_setOf_eq]
  constructor 
  · -- Assume u in left side, need to prove in right side
    rintro ⟨m, n, l, rfl⟩
    use 0
    use 3 * m + 2 * n + l
    use - (3 * m + 2 * n + l)
    ring
  · -- Assume u in right side, need to prove in left side
    rintro ⟨p, q, r, rfl⟩
    use 5 * p + 4 * q + 3 * r
    use - (5 * p + 4 * q + 3 * r)
    use 0 
    ring