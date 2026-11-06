import Mathlib

theorem inequalities_82200 :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 + c ^ 2 > 2 ∧ a ^ 3 + b ^ 3 + c ^ 3 < 2 ∧ a ^ 4 + b ^ 4 + c ^ 4 > 2 := by
  use 1.15, 0.7, 0.5
  constructor
  · norm_num  -- 0 < (1.15 : ℝ)
  constructor
  · norm_num  -- 0 < (0.7 : ℝ)
  constructor
  · norm_num  -- 0 < (0.5 : ℝ)
  constructor
  · norm_num  -- (1.15 : ℝ) ^ 2 + (0.7 : ℝ) ^ 2 + (0.5 : ℝ) ^ 2 > 2
  constructor
  · norm_num  -- (1.15 : ℝ) ^ 3 + (0.7 : ℝ) ^ 3 + (0.5 : ℝ) ^ 3 < 2
  · norm_num  -- (1.15 : ℝ) ^ 4 + (0.7 : ℝ) ^ 4 + (0.5 : ℝ) ^ 4 > 2