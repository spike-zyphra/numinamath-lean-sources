import Mathlib

open Real Set
open scoped Real

theorem inequalities_240277 (α : Real) (hα : α ∈ Icc 0 (π/2)) :
  (cos α)^2 + α * sin α ≥ 1 := by
  rcases hα with ⟨h1, h2⟩
  have h3 : 0 ≤ α := h1
  have h4 : α ≤ π / 2 := h2

  have h5 : sin α ≥ 0 := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith [h3, h4, Real.pi_pos]
    linarith [h3, h4, Real.pi_pos]
 
  have h7 : α ≥ sin α := by
    have h9 : sin α ≤ α := by
      apply sin_le
      all_goals linarith [Real.pi_pos]
    linarith
  
  have h8 : sin α * (α - sin α) ≥ 0 := by
    have h9 : sin α ≥ 0 := h5
    have h10 : α - sin α ≥ 0 := by linarith [h7]
    nlinarith
  
  have h9 : (cos α) ^ 2 + α * (sin α) - 1 ≥ 0 := by
    have h10 : (cos α) ^ 2 = 1 - (sin α) ^ 2 := by
      rw [Real.cos_sq']
    rw [h10]
    nlinarith [h8, Real.sin_sq_add_cos_sq α]
  
  linarith