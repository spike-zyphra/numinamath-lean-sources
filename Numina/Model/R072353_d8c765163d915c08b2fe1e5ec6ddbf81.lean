import Mathlib

theorem algebra_176209 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x * 1.13 = y * 0.5 + 310000) (h2 : x * 0.5 = y + 310000) :
    x = 6500000 ∧ y = 310000 := by
  norm_num at h1 h2 ⊢
  all_goals
    linarith