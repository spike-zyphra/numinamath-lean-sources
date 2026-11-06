import Mathlib

open Real Set
open scoped Real

theorem algebra_194886 (α β : ℝ) (h₀ : 0 < α) (h₁ : α < π / 2) (h₂ : 0 < β) (h₃ : β < π / 2)
    (h₄ : sin (α + β) = 2 * sin α) : β > α := by
  have h5 : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]
  rw [h5] at h₄
  by_contra h
  push_neg at h
  have h6 : sin β ≤ sin α := by
    apply sin_le_sin_of_le_of_le_pi_div_two
    all_goals
      linarith [pi_pos]
  have h7 : cos β ≥ cos α := by
    apply cos_le_cos_of_nonneg_of_le_pi
    all_goals
      linarith [pi_pos]
  have h8 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals
      linarith [pi_pos]
  have h9 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    all_goals
      linarith [pi_pos]
  have h10 : cos β > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    all_goals
      linarith [pi_pos]
  have h11 : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals
      linarith [pi_pos]
  nlinarith [h₄, h6, h7, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β,
    mul_pos h8 h9, mul_pos h8 h10, mul_pos h9 h11, mul_pos h8 h11, Real.sin_le_one α, Real.sin_le_one β, Real.cos_le_one α, Real.cos_le_one β, sq_nonneg (sin β - sin α), sq_nonneg (cos β - cos α)]