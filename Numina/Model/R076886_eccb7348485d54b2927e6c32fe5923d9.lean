import Mathlib

theorem inequalities_52090 (a b : ℝ) (ha : a ≠ b) :
    ∃ m n : ℤ, a * m + b * n < 0 ∧ b * m + a * n > 0 := by

  by_cases h : a < b
  · use 1, -1
    constructor
    · -- Show a * 1 + b * (-1) < 0
      have h1 : (a : ℝ) < (b : ℝ) := h
      norm_num
      all_goals linarith
    · -- Show b * 1 + a * (-1) > 0
      have h1 : (a : ℝ) < (b : ℝ) := h
      norm_num
      all_goals linarith
  · -- Case where ¬(a < b)
    have h2 : a > b := by 
      by_contra h'
      push_neg at h'
      have h' : a ≤ b := by linarith
      have h' : a = b := by
        linarith
      contradiction

    use -1, 1
    constructor
    · -- Show a * (-1) + b * (1) < 0
      have h2 : (a : ℝ) > (b : ℝ) := h2
      norm_num
      all_goals linarith
    · -- Show b * (-1) + a * (1) > 0
      have h2 : (a : ℝ) > (b : ℝ) := h2
      norm_num
      all_goals linarith