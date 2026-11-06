import Mathlib

theorem calculus_22400 (a b : ℝ) (h₀ : Real.sin a + Real.sin b = Real.sqrt (5 / 3)) (h₁ : Real.cos a + Real.cos b = 1) :
    Real.cos (a - b) = 1 / 3 := by
  have h2 : Real.sin a ^ 2 + Real.sin b ^ 2 + 2 * (Real.sin a * Real.sin b) = 5 / 3 := by
    calc
      Real.sin a ^ 2 + Real.sin b ^ 2 + 2 * (Real.sin a * Real.sin b) = (Real.sin a + Real.sin b) ^ 2 := by ring
      _ = (Real.sqrt (5 / 3)) ^ 2 := by rw [h₀]
      _ = 5 / 3 := by
        rw [Real.sq_sqrt]
        all_goals norm_num

  have h3 : Real.cos a ^ 2 + Real.cos b ^ 2 + 2 * (Real.cos a * Real.cos b) = 1 := by
    calc
      Real.cos a ^ 2 + Real.cos b ^ 2 + 2 * (Real.cos a * Real.cos b) = (Real.cos a + Real.cos b) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [h₁]
      _ = 1 := by norm_num

  have h4 : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  have h5 : Real.sin b ^ 2 + Real.cos b ^ 2 = 1 := Real.sin_sq_add_cos_sq b

  have h7 : Real.sin a * Real.sin b + Real.cos a * Real.cos b = 1 / 3 := by
    nlinarith [h2, h3, h4, h5]

  have h8 : Real.cos (a - b) = Real.cos a * Real.cos b + Real.sin a * Real.sin b := by
    rw [Real.cos_sub]

  linarith [h8, show Real.cos a * Real.cos b + Real.sin a * Real.sin b = 1 / 3 by linarith [h7]]