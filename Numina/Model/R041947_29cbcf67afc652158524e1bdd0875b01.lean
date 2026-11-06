import Mathlib

open Real Set
open scoped Real

theorem calculus_23272 (x : ℝ) :
  (cos x)^2 + (cos (π/3 + x))^2 + (cos (π/3 - x))^2 = 3/2 := by
  have h1 : cos (π / 3 + x) = 1 / 2 * cos x - Real.sqrt 3 / 2 * sin x := by
    rw [cos_add]
    have hcos : cos (π / 3) = 1 / 2 := by
      exact cos_pi_div_three
    have hsin : sin (π / 3) = Real.sqrt 3 / 2 := by
      exact sin_pi_div_three
    simp [hcos, hsin]
  have h2 : cos (π / 3 - x) = 1 / 2 * cos x + Real.sqrt 3 / 2 * sin x := by
    rw [cos_sub]
    have hcos : cos (π / 3) = 1 / 2 := by
      exact cos_pi_div_three
    have hsin : sin (π / 3) = Real.sqrt 3 / 2 := by
      exact sin_pi_div_three
    simp [hcos, hsin]
  rw [h1, h2]
  have h3 : (cos x) ^ 2 + (1 / 2 * cos x - Real.sqrt 3 / 2 * sin x) ^ 2 + (1 / 2 * cos x + Real.sqrt 3 / 2 * sin x) ^ 2 = 3 / 2 * (cos x ^ 2 + sin x ^ 2) := by
    nlinarith [Real.sqrt_pos.mpr (show (3: ℝ) > 0 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (3: ℝ) by norm_num), Real.sqrt_nonneg 3, sq_nonneg (cos x), sq_nonneg (sin x), sq_nonneg (Real.sqrt 3), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h4 : cos x ^ 2 + sin x ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq x
  rw [h3]
  rw [h4]
  all_goals linarith