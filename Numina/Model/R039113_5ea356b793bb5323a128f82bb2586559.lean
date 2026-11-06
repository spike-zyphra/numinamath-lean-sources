import Mathlib

open Real Set
open scoped Real

theorem algebra_275642 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) :
    (1 + 1 / sin α) * (1 + 1 / cos α) ≥ 3 + 2 * √2 := by
  rcases hα with ⟨h1, h2⟩
  have h3 : 0 < sin α := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    have h4 : π / 2 < π := by linarith [Real.pi_pos]
    have h5 : α < π := by linarith [h2, h4]
    linarith
  have h4 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have h5 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h6 : 0 < sin α * cos α := by
    nlinarith
  have h7 : (1 + 1 / sin α) * (1 + 1 / cos α) - (3 + 2 * √2) ≥ 0 := by
    have h8 : sin α ^ 2 + cos α ^ 2 = 1 := h5
    have h9 : 0 < sin α := h3
    have h10 : 0 < cos α := h4
    have h11 : sin α * cos α > 0 := by nlinarith
    have h12 : (1 + 1 / sin α) * (1 + 1 / cos α) - (3 + 2 * √2) ≥ 0 := by
      have h13 : (1 + 1 / sin α) * (1 + 1 / cos α) - (3 + 2 * √2) =
          ( (sin α + 1) * (cos α + 1) - (3 + 2 * √2) * (sin α * cos α) ) / (sin α * cos α) := by
        field_simp
        <;> ring
      rw [h13]
      have h14 : ( (sin α + 1) * (cos α + 1) - (3 + 2 * √2) * (sin α * cos α) ) ≥ 0 := by
        nlinarith [ sq_nonneg (sin α - cos α), sq_nonneg (sin α ^ 2 + cos α ^ 2 - 1), sq_nonneg (sin α ^ 2 - cos α ^ 2), sq_nonneg (sin α - Real.sqrt (1 / 2) ), sq_nonneg (cos α - Real.sqrt (1 / 2) ), Real.sqrt_pos.mpr (show (0 : Real) < (1 / 2 : Real) by norm_num), Real.sq_sqrt (show (0 : Real) ≤ (1 / 2 : Real) by norm_num), sq_nonneg (sin α * cos α - 1 / 2), Real.pi_gt_three, Real.sqrt_pos.mpr (show (0 : Real) < (2 : Real) by norm_num), Real.sq_sqrt (show (0 : Real) ≤ (2 : Real) by norm_num)]
      have h15 : sin α * cos α > 0 := h6
      apply div_nonneg
      linarith
      all_goals linarith
    linarith
  linarith [h7]