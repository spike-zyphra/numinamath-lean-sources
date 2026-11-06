import Mathlib

theorem algebra_211328 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x * 1.2 = y * 0.6) (h2 : x * 0.6 = y * 1.2) :
    max x y / min x y = 2 := by
  norm_num at h1 h2
  all_goals
    nlinarith