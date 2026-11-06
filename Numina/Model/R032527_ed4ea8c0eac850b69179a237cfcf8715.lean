import Mathlib

open Real Set
open scoped Real

theorem calculus_22272 : 4 * sin x * sin (π/3 - x) * sin (π/3 + x) = sin (3 * x) := by 
  have h1 : sin (π / 3) = Real.sqrt 3 / 2 := by 
    rw [sin_pi_div_three]

  have h2 : cos (π / 3) = 1 / 2 := by
    rw [cos_pi_div_three]

  have h3 : sin (π / 3 - x) = sin (π / 3) * cos x - cos (π / 3) * sin x := by 
    rw [sin_sub]

  have h4 : sin (π / 3 + x) = sin (π / 3) * cos x + cos (π / 3) * sin x := by 
    rw [sin_add]

  rw [h3, h4, h1, h2]

  have h5 : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by 
    rw [sin_three_mul]

  have h6 : 4 * sin x * (Real.sqrt 3 / 2 * cos x - 1 / 2 * sin x) * (Real.sqrt 3 / 2 * cos x + 1 / 2 * sin x) = 3 * sin x * cos x ^ 2 - sin x ^ 3 := by
    have h7 : (Real.sqrt 3 / 2 * cos x - 1 / 2 * sin x) * (Real.sqrt 3 / 2 * cos x + 1 / 2 * sin x) = 
            3 / 4 * (cos x) ^ 2 - 1 / 4 * (sin x) ^ 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (cos x - sin x), sq_nonneg (cos x), sq_nonneg (sin x), Real.sqrt_nonneg 3, sq_nonneg (cos x * sin x), sq_nonneg (Real.sqrt 3 * cos x), sq_nonneg (Real.sqrt 3 * sin x)]
    calc 
      4 * sin x * (Real.sqrt 3 / 2 * cos x - 1 / 2 * sin x) * (Real.sqrt 3 / 2 * cos x + 1 / 2 * sin x) 
        = 4 * sin x * ((Real.sqrt 3 / 2 * cos x - 1 / 2 * sin x) * (Real.sqrt 3 / 2 * cos x + 1 / 2 * sin x)) := by ring
      _ = 4 * sin x * (3 / 4 * (cos x) ^ 2 - 1 / 4 * (sin x) ^ 2) := by 
        rw [h7]
      _ = 3 * sin x * (cos x) ^ 2 - sin x ^ 3 := by 
        ring_nf

  have h7' : 3 * sin x * cos x ^ 2 - sin x ^ 3 = 3 * sin x - 4 * sin x ^ 3 := by 
    have h8 : cos x ^ 2 = 1 - sin x ^ 2 := by 
      have h9 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
      linarith 
    rw [h8]
    ring

  rw [h5]
  linarith [h6, h7', Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]