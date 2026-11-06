import Mathlib

open Real Set
open scoped Real

theorem inequalities_307987 (α : Real) (hα : α ∈ Ioo 0 (π/2)) :
    (1 + 1 / sin α) * (1 + 1 / cos α) ≥ 3 + 2 * sqrt 2 := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : 0 < sin α := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have h3 : sin α * cos α > 0 := mul_pos h1 h2
  have h4' : (1 + 1 / sin α) * (1 + 1 / cos α) =
    (sin α * cos α + sin α + cos α + 1) / (sin α * cos α) := by
    field_simp [h1, h2]
    <;> ring
  have h8 : (sin α * cos α + sin α + cos α + 1) ≥ (3 + 2 * Real.sqrt 2) * (sin α * cos α) := by
    have h6 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    nlinarith [sq_nonneg (sin α - cos α), sq_nonneg (sin α ^ 2 + cos α ^ 2 - 1), sq_nonneg (sin α - (1 : ℝ)/Real.sqrt 2), sq_nonneg (cos α - (1 : ℝ)/Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (sin α ^ 2 - cos α ^ 2), sq_nonneg (sin α + cos α - 1), sq_nonneg (sin α + cos α - Real.sqrt 2), h1, h2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), mul_pos h1 h2, sq_nonneg (sin α - cos α), Real.sin_sq_add_cos_sq α]
  have h5 : (sin α * cos α + sin α + cos α + 1) / (sin α * cos α) ≥ 3 + 2 * Real.sqrt 2 := by
    have h3_pos : sin α * cos α > 0 := h3
    apply (le_div_iff₀ h3_pos).mpr 
    nlinarith [Real.sqrt_nonneg 2, h8, mul_pos h1 h2]
  linarith [h5, h4']