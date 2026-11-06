import Mathlib

open Real

theorem algebra_145307 (α : Real) (hα : α ∈ Set.Ioo (π / 4) (π / 2)) :
    (cos α) ^ sin α < (cos α) ^ cos α ∧ (cos α) ^ cos α < (sin α) ^ cos α := by
  rcases hα with ⟨h1, h2⟩
  have h3 : 0 < π := Real.pi_pos
  have h4 : cos α < sin α := by
    have h5 : cos α < cos (π / 4) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [Real.pi_pos]
    have h6 : sin (π / 4) < sin α := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos]
    have h7 : cos (π / 4) = sin (π / 4) := by
      have h8 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      have h9 : sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      linarith
    have h8 : cos (π / 4) = sin (π / 4) := h7
    linarith [h5, h6, h7, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have h5 : cos α < 1 := by
    have h6 : cos α < cos (0 : ℝ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [Real.pi_pos]
    have h7 : cos (0 : ℝ) = 1 := Real.cos_zero
    linarith [h7, h6]
  have h6 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos, h1, h2]
    linarith [Real.pi_pos, h1, h2]
  have h7 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos, h1, h2]
    linarith [Real.pi_pos, h1, h2]
  have h10 : (cos α) ^ sin α < (cos α) ^ cos α := by
    have h11 : cos α < 1 := h5
    have h12 : 0 < cos α := h6
    have h13 : sin α > cos α := h4
    have h14 : (cos α) ^ sin α < (cos α) ^ cos α := by
      apply Real.rpow_lt_rpow_of_exponent_gt
      all_goals
      try linarith
      try linarith
    linarith
  have h11 : (cos α) ^ cos α < (sin α) ^ cos α := by
    have h12 : cos α < sin α := h4
    have h13 : 0 < cos α := h6
    have h14 : 0 < sin α := h7
    have h15 : cos α ^ cos α < sin α ^ cos α := by
      apply Real.rpow_lt_rpow
      all_goals
      try linarith
      try linarith
    linarith
  constructor
  · linarith [h10]
  · linarith [h11]