import Mathlib

open Real Set
open scoped Real

theorem calculus_22560 (α β : ℝ) (h : cos α / cos β + sin α / sin β = -1) (hc : cos β ≠ 0) (hs : sin β ≠ 0) (gc : cos α ≠ 0) (gs : sin α ≠ 0):
    cos β ^ 3 / cos α + sin β ^ 3 / sin α = 1 := by
  have h1 : cos α * sin β + sin α * cos β = -cos β * sin β := by
    have h2 : cos β ≠ 0 := hc
    have h3 : sin β ≠ 0 := hs
    field_simp [h2, h3] at h ⊢
    linarith
  have eq1 : cos α * sin β + sin α * cos β = -cos β * sin β := h1
  have eq2 : cos β ^ 3 * sin α + sin β ^ 3 * cos α = cos α * sin α := by
    have eq3 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    have eq4 : sin β ^ 2 + cos β ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq β
    have eq5 : cos α * sin β + sin α * cos β = -cos β * sin β := eq1
    nlinarith [sq_nonneg (sin α - cos α), sq_nonneg (sin β - cos β), 
      sq_pos_of_ne_zero (show cos α ≠ 0 by exact_mod_cast (show cos α ≠ 0 by tauto)), 
      sq_pos_of_ne_zero (show sin α ≠ 0 by exact_mod_cast (show sin α ≠ 0 by tauto)), 
      sq_pos_of_ne_zero (show cos β ≠ 0 by exact_mod_cast (show cos β ≠ 0 by tauto)), 
      sq_pos_of_ne_zero (show sin β ≠ 0 by exact_mod_cast (show sin β ≠ 0 by tauto)), 
      Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
      sq_nonneg (sin α - sin β), sq_nonneg (cos α - cos β)]
  have eq3 : cos β ^ 3 / cos α + sin β ^ 3 / sin α = 1 := by
    have eq3 : cos β ^ 3 * sin α + sin β ^ 3 * cos α = cos α * sin α := eq2
    have h4 : cos α ≠ 0 := by
      tauto
    have h5 : sin α ≠ 0 := by
      tauto
    have h6 : cos β ≠ 0 := by
      tauto
    have h7 : sin β ≠ 0 := by
      tauto
    field_simp [h4, h5, h6, h7]
    linarith [eq3]
  exact_mod_cast eq3