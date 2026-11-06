import Mathlib

theorem number_theory_214691 :
    {u : ℤ | ∃ m n l, u = 12 * m + 8 * n + 4 * l} =
    {u : ℤ | ∃ p q r, u = 20 * p + 16 * q + 12 * r} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume u ∈ M
    rintro ⟨m, n, l, rfl⟩
    exact ⟨3 * m + 2 * n + l, -(3 * m + 2 * n + l), 0, by ring⟩
  · -- Assume u ∈ N
    rintro ⟨p, q, r, rfl⟩
    exact ⟨p, 0, 5 * p + 4 * q + 3 * r - 3 * p, by ring⟩