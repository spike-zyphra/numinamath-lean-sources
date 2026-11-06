import Mathlib

open Real Set
open scoped Real

theorem inequalities_225993 (x : Real) :
  |2 * sin x + sin (2 * x)| < (3 + 2 * sqrt 2) / 2 := by
  have h1 : sin (2 * x) = 2 * sin x * cos x := by
    rw [sin_two_mul]
  rw [h1]
  have h2 : 2 * sin x + 2 * sin x * cos x < (3 + 2 * sqrt 2) / 2 := by
    nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x - cos x), 
      sq_nonneg (sin x + cos x), sq_nonneg (sin x - sqrt 2 / 2), 
      sq_nonneg (cos x - sqrt 2 / 2), mul_self_nonneg (sin x - sqrt 2 / 2), 
      mul_self_nonneg (cos x - sqrt 2 / 2), 
      Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
      Real.sqrt_nonneg 2, Real.sin_sq_add_cos_sq x, 
      sq_nonneg (sqrt 2 ^ 2 - 2)]
  have h3 : - ((3 + 2 * sqrt 2) / 2) < 2 * sin x + 2 * sin x * cos x := by
    nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x - cos x), 
      sq_nonneg (sin x + cos x), sq_nonneg (sin x - sqrt 2 / 2), 
      sq_nonneg (cos x - sqrt 2 / 2), mul_self_nonneg (sin x - sqrt 2 / 2), 
      mul_self_nonneg (cos x - sqrt 2 / 2), 
      Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
      Real.sqrt_nonneg 2, Real.sin_sq_add_cos_sq x, 
      sq_nonneg (sqrt 2 ^ 2 - 2)]
  apply abs_lt.mpr
  constructor <;> nlinarith [h2, h3]