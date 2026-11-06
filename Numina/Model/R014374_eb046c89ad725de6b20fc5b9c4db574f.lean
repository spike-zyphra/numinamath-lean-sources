import Mathlib

open Real

theorem algebra_13511 : sin (75 * π / 180) = (sqrt 6 + sqrt 2) / 4 := by
  have h1 : 75 * π / 180 = π / 4 + π / 6 := by 
    ring_nf
  rw [h1]
  have h2 : sin (π / 4 + π / 6) = sin (π / 4) * cos (π / 6) + cos (π / 4) * sin (π / 6) := by 
    rw [sin_add]
  rw [h2]
  have h3 : sin (π / 4) = Real.sqrt 2 / 2 := by 
    rw [sin_pi_div_four]
  have h4 : cos (π / 6) = Real.sqrt 3 / 2 := by 
    exact cos_pi_div_six
  have h5 : cos (π / 4) = Real.sqrt 2 / 2 := by 
    rw [cos_pi_div_four]
  have h6 : sin (π / 6) = 1 / 2 := by 
    exact sin_pi_div_six
  rw [h3, h4, h5, h6]
  have h7 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
    calc 
      Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
      _ = Real.sqrt 2 * Real.sqrt 3 := by 
        rw [Real.sqrt_mul (by norm_num)]
  have eq1 : (Real.sqrt 2 / 2) * (Real.sqrt 3 / 2) + (Real.sqrt 2 / 2) * (1 / 2) = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
    have eq2 : (Real.sqrt 2 / 2) * (Real.sqrt 3 / 2) = Real.sqrt 6 / 4 := by 
      have eq3 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := h7
      rw [eq3]
      ring_nf
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have eq4 : (Real.sqrt 2 / 2) * (1 / 2) = Real.sqrt 2 / 4 := by
      ring_nf
    linarith [eq2, eq4]
  linarith [eq1]