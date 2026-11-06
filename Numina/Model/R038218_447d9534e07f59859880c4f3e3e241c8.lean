import Mathlib

theorem number_theory_146853 (n : ℕ) :
    (1 / 6 : ℝ) < (n / 60 : ℝ) ∧ (n / 60 : ℝ) < (1 / 5 : ℝ) ↔ n = 11 := by
  constructor
  · -- Assume the expression is between 1/6 and 1/5, prove n = 11
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : (n : ℝ) > (10 : ℝ) := by
      nlinarith
    have h4 : n > 10 := by
      by_contra h4
      push_neg at h4
      have : n ≤ 10 := by linarith
      have h5 : (n : ℝ) ≤ (10 : ℝ) := by
        exact_mod_cast (show (n : ℕ) ≤ (10 : ℕ) from by linarith)
      linarith
    have h5 : (n : ℝ) < (12 : ℝ) := by
      nlinarith
    have h6 : n < 12 := by
      by_contra h6
      push_neg at h6
      have : n ≥ 12 := by linarith
      have h7 : (n : ℝ) ≥ (12 : ℝ) := by
        exact_mod_cast (show (n : ℕ) ≥ (12 : ℕ) from by linarith)
      linarith
    have h7 : n = 11 := by
      omega
    exact h7
  · -- Assume n = 11, prove the expression is between 1/6 and 1/5
    intro h7
    rw [h7]
    constructor
    · norm_num
    · norm_num