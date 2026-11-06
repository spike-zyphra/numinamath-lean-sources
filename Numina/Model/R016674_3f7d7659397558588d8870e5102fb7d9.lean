import Mathlib

open Real Set
open scoped Real

theorem inequalities_154096 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) :
  tan α + cot α + 1 / cos α + 1 / sin α ≥ 2 * (sqrt 2 + 1) := by
  rcases hα with ⟨h1, h2⟩
  have h3 : sin α > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have h4 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor 
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have eq3 : tan α + cot α + 1 / cos α + 1 / sin α = (sin α + 1) / cos α + (cos α + 1) / sin α := by
    have htan : tan α = sin α / cos α := by
      rw [Real.tan_eq_sin_div_cos]
    have hcot : cot α = cos α / sin α := by
      rw [Real.cot_eq_cos_div_sin]
    rw [htan, hcot]
    <;> field_simp [show sin α ≠ 0 by linarith [h3], show cos α ≠ 0 by linarith [h4]]
    <;> ring_nf 
  rw [eq3] at *
  have h7 : sin α * cos α > 0 := by 
    nlinarith
  suffices 1 + sin α + cos α ≥ 2 * (sqrt 2 + 1) * (sin α * cos α) by
    have h5 : sin α ≠ 0 := by linarith [h3]
    have h6 : cos α ≠ 0 := by linarith [h4]
    have h7 : ((sin α + 1) * sin α + (cos α + 1) * cos α - 2 * (sqrt 2 + 1) * (sin α * cos α)) / (sin α * cos α) ≥ 0 := by
      apply div_nonneg
      nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (sin α - cos α), sq_nonneg (sin α + cos α - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sin α ^ 2 - cos α ^ 2)]
      all_goals nlinarith
    have h8 : (sin α + 1) / cos α + (cos α + 1) / sin α - 2 * (sqrt 2 + 1) = ((sin α + 1) * sin α + (cos α + 1) * cos α - 2 * (sqrt 2 + 1) * (sin α * cos α)) / (sin α * cos α) := by 
      field_simp [h5, h6]
      ring
    have h9 : (sin α + 1) / cos α + (cos α + 1) / sin α - 2 * (sqrt 2 + 1) ≥ 0 := by 
      linarith [h8, h7]
    linarith
  nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : Real) < 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num), 
          sq_nonneg (sin α - cos α), Real.sin_sq_add_cos_sq α, 
          sq_nonneg (sin α + cos α - Real.sqrt 2), 
          mul_pos h3 h4, 
          sq_nonneg (sin α * cos α - (Real.sqrt 2 / 2) / 2), 
          Real.sin_sq_add_cos_sq α, 
          sq_nonneg (sin α ^ 2 - cos α ^ 2)
          ]