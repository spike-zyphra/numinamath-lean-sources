import Mathlib

theorem algebra_222799 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a = 1 / 16) (h2 : b = 1 / 20) (h3 : (1 + 20 / 100) * a * 10 = (1 - 47.25 / 100) * b * 10) :
    a * 10 + b * 10 = 1100 := by
  rw [h1, h2] at h3
  norm_num at h3 ⊢
  all_goals linarith