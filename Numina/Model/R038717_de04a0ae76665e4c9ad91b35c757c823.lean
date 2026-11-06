import Mathlib

theorem number_theory_261447 {M N : Set ℤ} (hM : M = {u : ℤ | ∃ m n l, u = 12 * m + 8 * n + 4 * l})
  (hN : N = {u : ℤ | ∃ p q r, u = 20 * p + 16 * q + 12 * r}) : M = N := by
  ext u
  simp only [hM, hN, Set.mem_setOf_eq]
  constructor
  · -- Assume u ∈ M, prove u ∈ N
    rintro ⟨m, n, l, h⟩
    use (3 * m + 2 * n + l)
    use -(3 * m + 2 * n + l)
    use 0
    all_goals
      ring_nf at h ⊢
      <;> omega
  · -- Assume u ∈ N, prove u ∈ M
    rintro ⟨p, q, r, h⟩
    use 0
    use 0
    use (5 * p + 4 * q + 3 * r)
    all_goals
      ring_nf at h ⊢
      <;> omega