import Mathlib

theorem number_theory_159911 (n : ℕ) :
    IsSquare (n^2 + n + 1) ↔ n = 0 := by
  constructor
  · -- Assume n^2 + n + 1 is a square, prove n = 0
    rintro h
    rcases h with ⟨k, hk⟩
    by_cases h2 : n > 0
    · -- Assume n > 0
      have h3 : k > n := by
        by_contra h'
        push_neg at h'
        have h4 : k ≤ n := by linarith
        have h5 : k ^ 2 ≤ n ^ 2 := by nlinarith [show k ≤ n by linarith]
        nlinarith [show k ^ 2 = n ^ 2 + n + 1 by linarith [hk]]
      have h4 : k ≤ n + 1 := by
        nlinarith [sq_nonneg (k - (n + 1 : ℕ)), sq_nonneg ((n + 1 : ℕ) - k), show k ^ 2 = n ^ 2 + n + 1 by linarith [hk]]
      have h5 : k = n + 1 := by
        nlinarith
      rw [h5] at hk
      nlinarith [h2]
    · -- n ≤ 0, so n = 0
      have h' : n = 0 := by linarith
      exact_mod_cast h'
  · -- Assume n = 0, prove IsSquare
    intro h
    rw [h]
    exact ⟨1, by norm_num⟩