import Mathlib

open Real Set
open scoped Real

theorem inequalities_247036 (α β : ℝ) (h₀ : sin β = 3 / 4 * sin α) (h₁ : α > 0 ∧ α ≤ π / 2 ∧ β > 0) :
    β > α / 2 := by

  rcases h₁ with ⟨hα1, hα2, hβ1⟩
  by_contra h
  push_neg at h
  have h3 : α / 2 > 0 := by linarith
  have h4 : α / 2 ≤ π / 4 := by
    nlinarith [hα2, Real.pi_pos]
  have h5 : sin β ≤ sin (α / 2) := by
    have hβ2 : β ≤ α / 2 := by linarith [h]
    have hα6 : α / 2 > 0 := h3
    have hα7 : β ≤ α / 2 := hβ2
    have hα11 : β > 0 := by linarith [hβ1]
    have hα8 : sin β ≤ sin (α / 2) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      all_goals
        nlinarith [hα6, hβ1, hα7, Real.pi_pos]
    linarith
  have h6 : 3 / 4 * sin α ≤ sin (α / 2) := by
    nlinarith [h₀, h5]
  have h7 : sin α = 2 * sin (α / 2) * cos (α / 2) := by
    rw [←sin_two_mul]
    ring
  have h8 : sin (α / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals
      nlinarith [h3, Real.pi_pos]
  have h9 : cos (α / 2) ≤ 2 / 3 := by
    nlinarith [h6, h7, h8, sq_nonneg (cos (α / 2) - 2 / 3), Real.cos_sq_add_sin_sq (α / 2)]
  have h10 : cos (α / 2) > 2 / 3 := by
    have hα3 : α / 2 ≤ π / 4 := h4
    have hα4 : cos (α / 2) ≥ cos (π / 4) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      all_goals
        nlinarith [h3, Real.pi_pos, hα3]
    have h11 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    have h12 : Real.sqrt 2 / 2 > 2 / 3 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 - 1.3333333333333333)]
    nlinarith [hα4, h11, h12]
  linarith [h9, h10]