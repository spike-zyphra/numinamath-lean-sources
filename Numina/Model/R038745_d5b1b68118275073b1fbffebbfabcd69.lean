import Mathlib

open Real

theorem algebra_143377 (α : ℝ) (hα : α ∈ Set.Ioo (π / 4) (π / 2)) :
    (cos α) ^ sin α < (cos α) ^ cos α ∧ (cos α) ^ cos α < (sin α) ^ cos α := by
  rcases hα with ⟨h1, h2⟩
  have h3 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor
    all_goals
      linarith [h1, h2, Real.pi_pos]
  have h4 : 0 < sin α := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals
      linarith [h1, h2, Real.pi_pos]
  have h5 : sin α > cos α := by
    have h6 : sin α > sin (π / 4) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith [h1, h2, Real.pi_pos]
    have h7 : cos α < cos (π / 4) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals
        linarith [h1, h2, Real.pi_pos]
    have h8 : sin (π / 4) = cos (π / 4) := by
      rw [show sin (π / 4) = sqrt 2 / 2 by rw [sin_pi_div_four]]
      rw [show cos (π / 4) = sqrt 2 / 2 by rw [cos_pi_div_four]]
    linarith [h6, h7, h8]
  have h9 : sin α < 1 := by
    have h10 : sin α < sin (π / 2) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith [h1, h2, Real.pi_pos]
    have h11 : sin (π / 2) = 1 := by
      rw [sin_pi_div_two]
    linarith [h10, h11]
  have h11 : cos α < 1 := by
    nlinarith [h5, h9, Real.sin_sq_add_cos_sq α]
  have h10 : (cos α) ^ sin α < (cos α) ^ cos α := by
    apply Real.rpow_lt_rpow_of_exponent_gt
    all_goals
      try linarith [h3, h11, h5]
  have h13 : (cos α) ^ cos α < (sin α) ^ cos α := by
    apply Real.rpow_lt_rpow
    all_goals
      try linarith [h3, h4, h5, h11]
  constructor
  · -- Prove (cos α) ^ sin α < (cos α) ^ cos α
    linarith [h10]
  · -- Prove (cos α) ^ cos α < (sin α) ^ cos α
    linarith [h13]