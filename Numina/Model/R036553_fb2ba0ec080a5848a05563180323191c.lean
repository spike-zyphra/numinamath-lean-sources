import Mathlib

theorem algebra_171248 (m1 m2 : ℝ) (h₀ : m1 = 2) (h₁ : m2 > 0)
    (h₂ : (7 * 2 + 5 * 2) / (7 + 5) = m2 / 4) (h₃ : (7 * 2 + 5 * 2) / (7 + 5) = 3 * 2 / 4) :
    m2 = 10.75 := by
  norm_num at h₃ 
  all_goals
  linarith