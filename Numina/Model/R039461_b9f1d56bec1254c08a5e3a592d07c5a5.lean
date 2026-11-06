import Mathlib

open Real Set

theorem inequalities_108193 (x y z : ℝ) (h : sin x + sin y + sin z ≥ 3 / 2) :
    sin (x - π / 6) + sin (y - π / 6) + sin (z - π / 6) ≥ 0 := by
  have h1 : sin (x - π / 6) = sin x * cos (π / 6) - cos x * sin (π / 6) := by
    rw [sin_sub]
  have h2 : sin (y - π / 6) = sin y * cos (π / 6) - cos y * sin (π / 6) := by
    rw [sin_sub]
  have h3 : sin (z - π / 6) = sin z * cos (π / 6) - cos z * sin (π / 6) := by
    rw [sin_sub]
  rw [h1, h2, h3]
  have h4 : cos (π / 6) = Real.sqrt 3 / 2 := by
    rw [cos_pi_div_six]
  have h5 : sin (π / 6) = 1 / 2 := by
    rw [sin_pi_div_six]
  rw [h4, h5]
  have h7 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    all_goals
      norm_num
  nlinarith [sq_nonneg (sin x - 1 / 2), sq_nonneg (sin y - 1 / 2), sq_nonneg (sin z - 1 / 2),
    sq_nonneg (cos x - Real.sqrt 3 / 2), sq_nonneg (cos y - Real.sqrt 3 / 2), sq_nonneg (cos z - Real.sqrt 3 / 2),
    Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0),
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3),
    sq_nonneg (sin x ^ 2 + sin y ^ 2 + sin z ^ 2 - 3 / 4),
    sq_nonneg (cos x ^ 2 + cos y ^ 2 + cos z ^ 2 - 3 / 4),
    Real.sqrt_nonneg 3,
    sq_nonneg (sin x - cos x * Real.sqrt 3 / 3), sq_nonneg (sin y - cos y * Real.sqrt 3 / 3), sq_nonneg (sin z - cos z * Real.sqrt 3 / 3),
    Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z
  ]