import Mathlib
open Real

theorem algebra_8734: sin (arcsin 0.7 + arcsin 0.3) * cos (arcsin 0.3 - arcsin 0.7 - π / 2) = -0.4 := by

  let a := arcsin 0.7
  let b := arcsin 0.3

  have h1 : sin (a + b) = sin a * cos b + cos a * sin b := by
    rw [sin_add]

  have h2 : sin a = 0.7 := by
    rw [show a = arcsin 0.7 by rfl]
    rw [sin_arcsin]
    all_goals norm_num

  have h3 : sin b = 0.3 := by
    rw [show b = arcsin 0.3 by rfl]
    rw [sin_arcsin]
    all_goals norm_num

  have h4 : cos a = Real.sqrt (1 - (0.7 : ℝ) ^ 2) := by
    rw [show a = arcsin 0.7 by rfl]
    rw [cos_arcsin]

  have h5 : cos b = Real.sqrt (1 - (0.3 : ℝ) ^ 2) := by
    rw [show b = arcsin 0.3 by rfl]
    rw [cos_arcsin]

  have h6 : cos (b - a - π / 2) = sin (b - a) := by
    have h7 : cos (b - a - π / 2) = sin (b - a) := by
      have h8 : b - a - π / 2 = (b - a) - π / 2 := by ring
      rw [h8]
      have h9 : cos ((b - a) - π / 2) = sin (b - a) := by
        rw [cos_sub_pi_div_two]
      exact h9
    exact h7

  have h7 : sin (b - a) = sin b * cos a - cos b * sin a := by
    rw [sin_sub]

  have eq1 : sin (a + b) = 0.7 * Real.sqrt (1 - (0.3 : ℝ) ^ 2) + Real.sqrt (1 - (0.7 : ℝ) ^ 2) * 0.3 := by
    rw [h1, h2, h3, h4, h5]
    all_goals ring

  have eq2 : cos (b - a - π / 2) = 0.3 * Real.sqrt (1 - (0.7 : ℝ) ^ 2) - Real.sqrt (1 - (0.3 : ℝ) ^ 2) * 0.7 := by
    rw [h6, h7, h3, h4, h5, h2]
    all_goals ring

  calc
    sin (arcsin 0.7 + arcsin 0.3) * cos (arcsin 0.3 - arcsin 0.7 - π / 2)
      = sin (a + b) * cos (b - a - π / 2) := by simp [a,b]
    _ = (0.7 * Real.sqrt (1 - (0.3 : ℝ) ^ 2) + Real.sqrt (1 - (0.7 : ℝ) ^ 2) * 0.3) * (0.3 * Real.sqrt (1 - (0.7 : ℝ) ^ 2) - Real.sqrt (1 - (0.3 : ℝ) ^ 2) * 0.7) := by
      rw [eq1, eq2]
    _ = - (0.4 : ℝ) := by
      have h8 : Real.sqrt (1 - (0.7 : ℝ) ^ 2) = Real.sqrt 0.51 := by
        rw [show (1 - (0.7 : ℝ) ^ 2 : ℝ) = (0.51 : ℝ) by norm_num]
      have h9 : Real.sqrt (1 - (0.3 : ℝ) ^ 2) = Real.sqrt 0.91 := by
        rw [show (1 - (0.3 : ℝ) ^ 2 : ℝ) = (0.91 : ℝ) by norm_num]
      rw [h8, h9]
      nlinarith [Real.sqrt_nonneg (0.51 : ℝ), Real.sqrt_nonneg (0.91 : ℝ), 
        Real.sq_sqrt (show (0.51 : ℝ) ≥ 0 by norm_num), 
        Real.sq_sqrt (show (0.91 : ℝ) ≥ 0 by norm_num), 
        Real.sqrt_nonneg (0.51 : ℝ), Real.sqrt_nonneg (0.91 : ℝ), 
        sq_nonneg (Real.sqrt (0.51 : ℝ) - Real.sqrt (0.91 : ℝ)), 
        sq_nonneg (Real.sqrt (0.51 : ℝ) * Real.sqrt (0.91 : ℝ))
      ]
    _ = -0.4 := by norm_num