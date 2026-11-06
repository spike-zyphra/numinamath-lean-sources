import Mathlib

open Real Set
open scoped Real

theorem inequalities_6220 (x : Real) :
  sin (2 * x) + 2 * cos x ≤ 3 * sqrt 3 / 2 := by
  have h1 : sin (2 * x) = 2 * sin x * cos x := by
    rw [sin_two_mul]
  rw [h1]
  have h2 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  nlinarith [sq_nonneg (cos x - Real.sqrt 3 / 2), sq_nonneg (sin x - 1 / 2), 
          sq_nonneg (sin x + 1 / 2), sq_nonneg (cos x + Real.sqrt 3 / 2), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          h2, 
          sq_nonneg (cos x * (sin x - 1 / 2)), 
          sq_nonneg (sin x - 1 / 2), 
          sq_nonneg (cos x - Real.sqrt 3 / 2)
]