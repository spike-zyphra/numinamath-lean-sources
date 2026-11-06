import Mathlib

open Real Set
open scoped Real

theorem inequalities_250912 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) :
    sin α < tan α ∧
    (deriv sin α > 0 ∧ deriv tan α > 0 ∧
     deriv tan α > deriv sin α) := by
  rcases hα with ⟨h1, h2⟩
  have h3 : 0 < α := by linarith
  have h4 : α < π / 2 := by linarith
  have h5 : 0 < sin α := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h3, h4, Real.pi_pos]
    linarith [h3, h4, Real.pi_pos]
  have h6 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h3, h4, Real.pi_pos]
    linarith [h3, h4, Real.pi_pos]
  have h7 : cos α < 1 := by
    have h8 : cos α < cos (0 : Real) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [h3, h4, Real.pi_pos]
    have h9 : cos (0 : Real) = 1 := Real.cos_zero
    linarith [h8, h9]
  have h8 : sin α < tan α := by
    have htan : tan α = sin α / cos α := by rw [tan_eq_sin_div_cos]
    rw [htan]
    have h9 : 0 < cos α := h6
    have h10 : sin α > 0 := h5
    have h11 : cos α < 1 := h7
    have h12 : 1 - cos α > 0 := by linarith
    have h13 : (sin α * (1 - cos α)) / cos α > 0 := by
      apply div_pos
      · -- Show sin α * (1 - cos α) > 0
        have hsin : sin α > 0 := h5
        have h14 : 1 - cos α > 0 := h12
        nlinarith
      · -- Show cos α > 0
        linarith [h6]
    have h14 : sin α / cos α - sin α = (sin α * (1 - cos α)) / cos α := by
      field_simp
      <;> ring
    nlinarith [show sin α / cos α - sin α > 0 by
      rw [h14]
      nlinarith [h13]
    ]
  have h9 : deriv sin α = cos α := by simp
  have h10 : deriv tan α = 1 / (cos α ^ 2) := by
    rw [Real.deriv_tan]
    all_goals try tauto
  have h11 : deriv sin α > 0 := by 
    rw [h9]
    nlinarith [h6, h7]
  have h12 : deriv tan α > 0 := by 
    rw [h10]
    positivity
  have h13 : deriv tan α > deriv sin α := by 
    rw [h10, h9]
    have h14 : cos α > 0 := h6
    have h15 : cos α < 1 := h7
    have h16 : cos α ^ 2 > 0 := by nlinarith
    have h17 : 1 / (cos α ^ 2) > cos α := by
      have h18 : cos α ^ 2 > 0 := by nlinarith
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (cos α - 1), sq_pos_of_pos h14]
    nlinarith
  constructor
  · exact h8
  constructor
  · exact h11
  constructor
  · exact h12
  · exact h13