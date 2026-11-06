import Mathlib

theorem algebra_319831 {x : ℝ} (hx : x = (23 + Real.sqrt 469) / 5) :
    25 * x ^ 4 - 1996 * x ^ 2 + 144 = 0 := by

  have h1 : 5 * x^2 - 46 * x + 12 = 0 := by
    rw [hx]
    nlinarith [Real.sqrt_nonneg 469, Real.sq_sqrt (show (0 : ℝ) ≤ 469 by norm_num)]

  have h2 : 25 * x ^4 = (46 * x - 12) ^2 := by
    have eq1 : 5 * x ^2 = 46 * x - 12 := by
      linarith [h1]
    calc
      25 * x ^4 = (5 * x ^2) ^2 := by ring
      _ = (46 * x - 12) ^2 := by rw [eq1]

  nlinarith [h2, h1, sq_nonneg (x * 5 - 23), Real.sqrt_nonneg 469, Real.sq_sqrt (show (0 : ℝ) ≤ 469 by norm_num)]