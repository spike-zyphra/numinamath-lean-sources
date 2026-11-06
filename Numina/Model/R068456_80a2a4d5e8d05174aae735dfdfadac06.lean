import Mathlib

theorem algebra_314463 (x1 x2 y1 y2 : ℝ)
    (h1 : x1^2 + 25 * x2^2 = 10)
    (h2 : x2 * y1 - x1 * y2 = 25)
    (h3 : x1 * y1 + 25 * x2 * y2 = 9 * Real.sqrt 55) :
    y1^2 + 25 * y2^2 = 2008 := by
  have h4 : (x2 * y1 - x1 * y2)^2 = 25^2 := by
    rw [h2]
  have h5 : (x1 * y1 + 25 * x2 * y2)^2 = (9 * Real.sqrt 55)^2 := by
    rw [h3]
  have h6 : (Real.sqrt 55) ^ 2 = 55 := Real.sq_sqrt (by norm_num)
  have h7 : (x1 * y1 + 25 * x2 * y2)^2 = 4455 := by
    rw [h5]
    have h8 : (9 * Real.sqrt 55)^2 = 9^2 * ((Real.sqrt 55) ^ 2) := by
      ring
    rw [h8]
    rw [h6]
    norm_num
  have h8 : (x2 * y1 - x1 * y2)^2 = 625 := by
    rw [h4]
    norm_num
  nlinarith [h1, h8, h7, Real.sqrt_nonneg 55]