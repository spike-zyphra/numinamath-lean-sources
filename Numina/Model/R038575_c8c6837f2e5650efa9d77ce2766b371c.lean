import Mathlib

open Real

theorem calculus_13792 : tan (π / 24) + tan (7 * π / 24) = 2 * sqrt 6 - 2 * sqrt 3 := by
  have h1 : tan (π / 24) + tan (7 * π / 24) = sin ((π / 24) + (7 * π / 24)) / (cos (π / 24) * cos (7 * π / 24)) := by
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
    have h2 : sin (π / 24) * cos (7 * π / 24) + cos (π / 24) * sin (7 * π / 24) = sin ((π / 24) + (7 * π / 24)) := by
      rw [sin_add]
      <;> ring
    have h3 : sin (π / 24) / cos (π / 24) + sin (7 * π / 24) / cos (7 * π / 24) =
        (sin (π / 24) * cos (7 * π / 24) + cos (π / 24) * sin (7 * π / 24)) / (cos (π / 24) * cos (7 * π / 24)) := by
      field_simp [(show cos (π / 24) ≠ 0 by
        have hcos1 : cos (π / 24) > 0 := by 
          apply cos_pos_of_mem_Ioo
          constructor <;> 
            linarith [Real.pi_pos]
        linarith
      ), (show cos (7 * π / 24) ≠ 0 by
        have hcos2 : cos (7 * π / 24) > 0 := by
          apply cos_pos_of_mem_Ioo
          constructor <;> 
            linarith [Real.pi_pos]
        linarith
      )
      ]
      <;> ring
    rw [h2] at h3
    linarith
  have h2 : sin ((π / 24) + (7 * π / 24)) = Real.sqrt 3 / 2 := by
    have : (π / 24 : ℝ) + (7 * π / 24 : ℝ) = Real.pi / 3 := by
      linarith [Real.pi_pos]
    rw [this]
    rw [sin_pi_div_three]
  have h3 : cos (π / 24) * cos (7 * π / 24) = (Real.sqrt 2 + 1) / 4 := by
    have h4 : cos (π / 24) * cos (7 * π / 24) = (cos ((7 * π / 24) + (π / 24)) + cos ((7 * π / 24) - (π / 24)) ) / 2 := by
      rw [cos_add, cos_sub]
      ring_nf
      <;> ring
    have h5 : cos ((7 * π / 24) + (π / 24)) = 1 / 2 := by
      have : (7 * π / 24 + π / 24 : ℝ) = Real.pi / 3 := by
        linarith [Real.pi_pos]
      rw [this]
      rw [cos_pi_div_three]
    have h6 : cos ((7 * π / 24) - (π / 24)) = Real.sqrt 2 / 2 := by
      have : (7 * π / 24 - π / 24 : ℝ) = Real.pi / 4 := by
        linarith [Real.pi_pos]
      rw [this]
      rw [cos_pi_div_four]
    rw [h4, h5, h6]
    <;> nlinarith 
    all_goals ring_nf <;> nlinarith
    all_goals ring_nf <;> nlinarith
  rw [h1, h2, h3]
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    have h : Real.sqrt 6 = Real.sqrt (2 * 3) := by
      norm_num
    rw [h]
    rw [Real.sqrt_mul (by norm_num)]
  rw [h6]
  have h4 : 0 < Real.sqrt 2 := by
    positivity
  have h5 : 0 < Real.sqrt 3 := by
    positivity
  field_simp [(show Real.sqrt 2 > 0 by positivity), (show Real.sqrt 3 > 0 by positivity)]
  <;> ring_nf <;> norm_num [Real.sq_sqrt, mul_add, mul_comm]
  <;> nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
      mul_pos (show (0 : ℝ) < Real.sqrt 2 by positivity) 
        (show (0 : ℝ) < Real.sqrt 3 by positivity)]
  all_goals linarith