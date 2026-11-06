import Mathlib

theorem algebra_187336 (n : ℕ) (hn : n ≥ 6) :
    (1 - (4 / 5 : ℝ)) * (1 - (1 / 2 : ℝ)) ^ (n - 1) ≤ 1 / 100 := by
  have h1 : (1 - (4 / 5 : ℝ)) = (1 / 5 : ℝ) := by norm_num
  have h2 : (1 - (1 / 2 : ℝ) ) = (1 / 2 : ℝ) := by norm_num
  rw [h1, h2]
  have h3 : (n : ℕ) ≥ 6 := hn
  have h4 : (1 / 5 : ℝ) * (1 / 2 : ℝ) ^ (n - 1) ≤ (1 / 100 : ℝ) := by
    have h7 : (n : ℕ) ≥ 6 := h3
    have h8 : (n - 1 : ℕ) ≥ 5 := by
      have : n ≥ 6 := h7
      omega
    have h999' : (5 : ℕ) ≤ (n - 1 : ℕ) := by linarith
    have h14 : (1 / 2 : ℝ) ^ (n - 1) ≤ (1 / 2 : ℝ) ^ (5 : ℕ) := by
      apply pow_le_pow_of_le_one
      all_goals norm_num
      all_goals
      omega
    have h15 : (1 / 5 : ℝ) * (1 / 2 : ℝ) ^ (n - 1) ≤ (1 / 5 : ℝ) * (1 / 2 : ℝ) ^ (5 : ℕ) := by
      apply mul_le_mul_of_nonneg_left
      linarith
      all_goals
      norm_num
    have h16 : (1 / 5 : ℝ) * (1 / 2 : ℝ) ^ (5 : ℕ) = (1 / 160 : ℝ) := by
      norm_num
    have h17 : (1 / 160 : ℝ) ≤ (1 / 100 : ℝ) := by
      norm_num
    linarith [h14, h15, h16, h17]
  linarith