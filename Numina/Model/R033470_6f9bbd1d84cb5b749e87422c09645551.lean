import Mathlib

theorem algebra_140477 {x : ℝ} (hx : x > 0) (h1 : 60 * x = 6 * 10 ^ 6) (h2 : 42 * x = 4.2 * 10 ^ 6)
    (h3 : 6200 = (60 * x - 6 * 10 ^ 6) * 0.001) :
    x = 0.95 := by
  norm_num at h1 h2 h3 ⊢
  linarith