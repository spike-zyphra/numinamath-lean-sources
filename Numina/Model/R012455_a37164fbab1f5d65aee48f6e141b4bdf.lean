import Mathlib

open Real Set
open scoped Real

theorem algebra_316543 (α : ℝ) (hα : α ∈ Ioc 0 (π / 2)) :
    sqrt (1 + 2 * sin α * cos α) + sqrt (1 - 2 * sin α * cos α) = 2 * cos α ∨
    sqrt (1 + 2 * sin α * cos α) + sqrt (1 - 2 * sin α * cos α) = 2 * sin α := by
  rcases hα with ⟨h1, h2⟩
  have h3 : 1 + 2 * sin α * cos α = (sin α + cos α) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have h4 : 1 - 2 * sin α * cos α = (sin α - cos α) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have h5 : sqrt (1 + 2 * sin α * cos α) = sin α + cos α := by
    rw [h3]
    have h6 : sin α ≥ 0 := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      linarith [pi_pos]
      linarith [pi_pos]
    have h7 : cos α ≥ 0 := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      linarith [pi_pos]
      linarith [pi_pos]
    have h8 : sin α + cos α ≥ 0 := by
      linarith
    rw [Real.sqrt_sq (show sin α + cos α ≥ 0 by linarith)]
  have h8 : sqrt (1 - 2 * sin α * cos α) = abs (sin α - cos α) := by
    rw [h4]
    have h8 : sqrt ((sin α - cos α) ^ 2) = abs (sin α - cos α) := by
      rw [Real.sqrt_sq_eq_abs]
    linarith
  rw [h5, h8]
  by_cases h : sin α ≤ cos α
  · -- sin α ≤ cos α
    have h9 : abs (sin α - cos α) = cos α - sin α := by
      rw [abs_of_nonpos (by linarith)]
      all_goals linarith
    left
    linarith [h9]
  · -- sin α > cos α
    have h10 : sin α > cos α := by
      linarith
    have h11 : abs (sin α - cos α) = sin α - cos α := by
      rw [abs_of_pos (by linarith [h10])]
      all_goals linarith
    right
    linarith [h11]