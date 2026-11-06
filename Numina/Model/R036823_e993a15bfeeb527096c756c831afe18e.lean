import Mathlib

open Real Set

theorem algebra_323161 (s t : ℝ) :
    (s + 7 - abs (cos t))^2 + (s - 2 * abs (sin t))^2 ≥ 18 := by
  have h1 : abs (cos t) ≥ 0 := by apply abs_nonneg
  have h2 : abs (sin t) ≥ 0 := by apply abs_nonneg
  have h4 : (abs (cos t)) ^ 2 + (abs (sin t)) ^ 2 = 1 := by
    have h5 : (cos t) ^ 2 + (sin t) ^ 2 = 1 := Real.cos_sq_add_sin_sq t
    have h6 : (abs (cos t)) ^ 2 = (cos t) ^ 2 := by
      rw [sq_abs]
    have h7 : (abs (sin t)) ^ 2 = (sin t) ^ 2 := by
      rw [sq_abs]
    rw [h6, h7]
    linarith
  nlinarith [sq_nonneg (s + 3), sq_nonneg (abs (cos t) - 1), sq_nonneg (abs (sin t) - 0), sq_nonneg (s - (-3)), sq_nonneg (s + 3 - (abs (sin t) - 0) * 2), sq_nonneg (s + 0 * abs (cos t)), sq_nonneg ((abs (cos t) - 1) * 0), sq_nonneg (s + 3), sq_nonneg (abs (cos t) - 1), sq_nonneg (abs (sin t) - 0), sq_nonneg (s + 3),
    mul_nonneg (abs_nonneg (cos t)) (abs_nonneg (sin t)), sq_nonneg (s + 3 - abs (cos t)), sq_nonneg (s - (2 * abs (sin t))), sq_nonneg (s * 0), sq_nonneg ((s - s) * 0), sq_nonneg (abs (cos t) ^ 2 - 1), sq_nonneg (abs (sin t) ^ 2 - 0), h1, h2
  ]