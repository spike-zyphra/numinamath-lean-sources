import Mathlib

open Real Set
open scoped Real

theorem inequalities_315089 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) :
    8 ≤ 1 / sin α + 3 * sqrt 3 / cos α := by
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

  have h5 : 1 / sin α + 3 * sqrt 3 / cos α - 8 ≥ 0 := by
    have h6 : sin α * cos α > 0 := mul_pos h3 h4
    have h7 : 1 / sin α + 3 * sqrt 3 / cos α - 8 = (cos α + 3 * sqrt 3 * sin α - 8 * sin α * cos α) / (sin α * cos α) := by
      field_simp
      ring
    rw [h7]
    apply div_nonneg
    nlinarith [sq_nonneg (sin α - 1 / 2), sq_nonneg (cos α - Real.sqrt 3 / 2), 
          sq_nonneg (sin α * cos α - Real.sqrt 3 / 4), 
          sq_nonneg (sin α - 1 / 2), sq_nonneg (cos α - Real.sqrt 3 / 2), 
          sq_nonneg (sin α * Real.sqrt 3 - cos α), 
          sq_nonneg (sin α - cos α / Real.sqrt 3), 
          Real.sqrt_nonneg 3, Real.sq_sqrt (show 3 ≥ 0 by norm_num), 
          Real.sin_sq_add_cos_sq α, 
          Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), 
          mul_pos h3 (show Real.sqrt 3 > 0 by positivity), 
          mul_pos h4 (show Real.sqrt 3 > 0 by positivity)]
    positivity

  linarith