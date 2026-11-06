import Mathlib

theorem algebra_290905 (t : ℝ) (ht : t > 0) (x : ℝ) (hx : 0 < x)
    (h1 : x + t / 2 = 20 / 100 * (x + t ^ 2 / 4)) (h2 : x + t ^ 2 / 4 = 50 / 100 * (x + t / 2)) :
    x = 3 := by 
  nlinarith [h1, h2, sq_nonneg (t - 3), sq_nonneg (t - 1), sq_nonneg (t - 4), sq_nonneg (t - 2)]