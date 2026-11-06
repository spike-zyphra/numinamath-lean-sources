import Mathlib

open Real Set
open scoped Real

theorem inequalities_232477 (α : ℝ) (hsin : sin α ≠ 0) (hcos : cos α ≠ 0) :
    (1 + abs (1 / sin α)) * (1 + abs (1 / cos α)) ≥ (1 + sqrt 2)^2 := by 
  have h1 : abs (1 / sin α) = 1 / abs (sin α) := by
    field_simp [abs_div, hsin]
  have h2 : abs (1 / cos α) = 1 / abs (cos α) := by
    field_simp [abs_div, hcos]
  rw [h1, h2]

  have h3 : abs (sin α) ^ 2 + abs (cos α) ^ 2 = 1 := by
    have h4 : sin α ^ 2 + cos α ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq α
    have h5 : abs (sin α) ^ 2 = sin α ^ 2 := by 
      rw [sq_abs]
    have h6 : abs (cos α) ^ 2 = cos α ^ 2 := by 
      rw [sq_abs]
    rw [h5, h6]
    linarith [h4]

  have h4 : abs (sin α) > 0 := by
    by_contra h
    push_neg at h
    have h5 : abs (sin α) = 0 := by linarith [abs_nonneg (sin α), h]
    have h6 : sin α = 0 := by 
      rw [abs_eq_zero] at h5 
      exact h5
    contradiction
  have h5 : abs (cos α) > 0 := by
    by_contra h
    push_neg at h
    have h6 : abs (cos α) = 0 := by linarith [abs_nonneg (cos α), h]
    have h7 : cos α = 0 := by 
      rw [abs_eq_zero] at h6 
      exact h6
    contradiction
  
  have h7 : (1 + 1 / abs (sin α)) * (1 + 1 / abs (cos α)) - (1 + sqrt 2)^2 ≥ 0 := by
    have h8 : abs (sin α) > 0 := h4
    have h9 : abs (cos α) > 0 := h5
    -- Expand inequality into a workable form without division
    have h10 : (1 + 1 / abs (sin α)) * (1 + 1 / abs (cos α)) - (1 + Real.sqrt 2)^2 =
        ( (abs (sin α) + 1) * (abs (cos α) + 1) - (1 + Real.sqrt 2)^2 * (abs (sin α) * abs (cos α)) ) / (abs (sin α) * abs (cos α)) := by
      field_simp [h8, h9]
      ring
    -- Prove denominator is positive
    have h11 : abs (sin α) * abs (cos α) > 0 := mul_pos h8 h9
    -- Prove numerator is positive
    have h12 : (abs (sin α) + 1) * (abs (cos α) + 1) - (1 + Real.sqrt 2)^2 * (abs (sin α) * abs (cos α)) ≥ 0 := by
      nlinarith [h3, sq_nonneg (abs (sin α) - abs (cos α)), sq_nonneg (abs (sin α) + abs (cos α) - Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), h8, h9]
    -- Final upper step
    rw [h10]
    apply div_nonneg h12 (by positivity)
  linarith [h7]