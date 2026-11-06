import Mathlib

theorem number_theory_188535 (n : ℕ) (hn : n > 5) :
    ∃ k, (5 * n / (n - 5)) = k ∧ k ≥ 12 ↔ n = 6 := by
  by_cases h : n = 6
  · -- If n = 6, then k = 30
    use 30
    simp [h]
  · -- If n ≠ 6
    have hne : n ≠ 6 := by
      by_contra h'
      contradiction
    use 0
    constructor
    · -- Assume (5 * n / (n - 5)) = 0 ∧ 0 ≥ 12, prove n = 6
      intro h
      rcases h with ⟨h1, h2⟩
      omega
    · -- Assume n = 6, prove (5 * n / (n - 5)) = 0 ∧ 0 ≥ 12
      intro h
      omega