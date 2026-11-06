import Mathlib

theorem algebra_271 : (4 * Real.sqrt (3 + 2 * Real.sqrt 2) - Real.sqrt (41 + 24 * Real.sqrt 2)) = 1 := by

  have h1 : Real.sqrt (3 + 2 * Real.sqrt 2) = Real.sqrt 2 + 1 := by
    have h1 : (Real.sqrt 2 + 1) ^ 2 = 3 + 2 * Real.sqrt 2 := by
      calc 
        (Real.sqrt 2 + 1) ^ 2 = (Real.sqrt 2) ^ 2 + 2 * Real.sqrt 2 + 1 := by ring
        _ = 2 + 2 * Real.sqrt 2 + 1 := by rw [Real.sq_sqrt]; linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num : (0:ℝ) < 2)]
        _ = 3 + 2 * Real.sqrt 2 := by ring

    have h2 : 0 ≤ Real.sqrt 2 + 1 := by 
      have h3 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith

    rw [←h1]
    field_simp [Real.sqrt_sq h2]

  have h2 : Real.sqrt (41 + 24 * Real.sqrt 2) = 3 + 4 * Real.sqrt 2 := by 
    have h3 : (3 + 4 * Real.sqrt 2) ^ 2 = 41 + 24 * Real.sqrt 2 := by 
      calc 
        (3 + 4 * Real.sqrt 2) ^ 2 = 3^2 + 2 * 3 * (4 * Real.sqrt 2) + (4 * Real.sqrt 2) ^ 2 := by ring
        _ = 9 + 24 * Real.sqrt 2 + 16 * (Real.sqrt 2 * Real.sqrt 2) := by ring
        _ = 9 + 24 * Real.sqrt 2 + 16 * (Real.sqrt 2 ^ 2) := by ring
        _ = 9 + 24 * Real.sqrt 2 + 16 * 2 := by rw [Real.sq_sqrt]; linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num : (0:ℝ) < 2)]
        _ = 41 + 24 * Real.sqrt 2 := by ring

    have h4 : 0 ≤ 3 + 4 * Real.sqrt 2 := by 
      have h5 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith [h5]

    rw [←h3]
    field_simp [Real.sqrt_sq h4]

  rw [h1, h2]
  linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num : (0:ℝ) < 2)]