import Mathlib

open Real Set
open scoped Real

theorem inequalities_211803 (φ : Real) (hφ : φ ∈ Ioo 0 (π/2)) :
    sin (cos φ) < cos φ ∧ cos φ < cos (sin φ) := by

  rcases hφ with ⟨hφ1, hφ2⟩
  have h1 : 0 < φ := hφ1
  have h2 : φ < π / 2 := hφ2
  have hcos1 : 0 < cos φ := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [h1, Real.pi_pos]
    · linarith [h2, Real.pi_pos]
  have hcos2 : cos φ < 1 := by
    have h3 : cos φ < cos (0 : ℝ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [h1, h2, Real.pi_pos]
    have h4 : cos (0 : ℝ) = 1 := Real.cos_zero
    linarith [h3, h4]

  have h3 : sin (cos φ) < cos φ := by
    have h4 : sin (cos φ) < cos φ := by
      apply sin_lt
      all_goals
        nlinarith [hcos1, Real.pi_gt_three, hcos2]
    linarith

  have hsin1 : 0 < sin φ := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals
      linarith [h1, h2, Real.pi_pos]
  have hsin2 : sin φ < φ := by
    have h4 : sin φ < φ := by
      apply sin_lt
      all_goals
        nlinarith [h1, Real.pi_gt_three, h2]
    linarith

  have h5 : cos φ < cos (sin φ) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    all_goals
      nlinarith [h1, h2, Real.pi_pos, hsin1, hsin2, Real.sin_sq_add_cos_sq φ, Real.sin_le_one φ, Real.cos_le_one φ, Real.sin_sq_add_cos_sq (φ), Real.sin_sq_add_cos_sq (sin φ)]

  constructor
  · linarith [h3]
  · linarith [h5]