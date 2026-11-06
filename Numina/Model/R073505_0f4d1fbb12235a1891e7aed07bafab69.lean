import Mathlib

open Real

theorem algebra_21449 : sqrt (41 + 24 * sqrt 2) = 3 + 4 * sqrt 2 := by
  have h1 : (3 + 4 * Real.sqrt 2) ^ 2 = 41 + 24 * Real.sqrt 2 := by
    calc
      (3 + 4 * Real.sqrt 2) ^ 2 = 3^2 + 2 * 3 * (4 * Real.sqrt 2) + (4 * Real.sqrt 2)^2 := by ring
      _ = 9 + 24 * Real.sqrt 2 + (4 * Real.sqrt 2)^2 := by ring
      _ = 9 + 24 * Real.sqrt 2 + 16 * (Real.sqrt 2 * Real.sqrt 2) := by ring
      _ = 9 + 24 * Real.sqrt 2 + 16 * (Real.sqrt 2 ^ 2) := by ring
      _ = 9 + 24 * Real.sqrt 2 + 16 * 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      _ = 41 + 24 * Real.sqrt 2 := by ring

  have h2 : 0 ≤ 3 + 4 * Real.sqrt 2 := by
    have h3 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith [h3]

  rw [←h1]
  field_simp [Real.sqrt_sq (show 0 ≤ 3 + 4 * Real.sqrt 2 by linarith [Real.sqrt_nonneg 2])]