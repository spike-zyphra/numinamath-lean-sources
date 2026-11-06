import Mathlib

open Real Set
open scoped Real

theorem calculus_22433 :
  IsLeast {θ : ℝ | 0 < θ ∧ sin (3 * θ) = cos (7 * θ)} (π / 20) := by
  constructor
  · -- Show that π/20 is in the set
    constructor
    · -- Show that π/20 > 0
      linarith [Real.pi_pos]
    · -- Show that sin(3 * π / 20) = cos(7 * π / 20)
      have h1 : sin (3 * (π / 20)) = cos (7 * (π / 20)) := by
        have h2 : cos (7 * (π / 20)) = sin (3 * (π / 20)) := by
          have h3 : 7 * (π / 20) = (Real.pi / 2) - (3 * (π / 20)) := by
            linarith [Real.pi_pos]
          rw [h3]
          rw [cos_pi_div_two_sub]
        linarith [h2]
      linarith [h1]
  · -- Show that π/20 is the least element in the set
    intro θ h
    rcases h with ⟨h_pos, h_eq⟩
    by_contra h'
    push_neg at h'
    have h3 : θ < π / 20 := h'
    have h4 : 3 * θ < 3 * (π / 20) := by nlinarith
    have h5 : 7 * θ < 7 * (π / 20) := by nlinarith
    have h6 : sin (3 * θ) < sin (3 * (π / 20)) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos, h_pos, h3]
    have h7 : cos (7 * θ) > cos (7 * (π / 20)) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [Real.pi_pos, h_pos, h3]
    have h8 : sin (3 * (π / 20)) = cos (7 * (π / 20)) := by
      have h2 : cos (7 * (π / 20)) = sin (3 * (π / 20)) := by
        have h3 : 7 * (π / 20) = (Real.pi / 2) - (3 * (π / 20)) := by
          linarith [Real.pi_pos]
        rw [h3]
        rw [cos_pi_div_two_sub]
      linarith [h2]
    nlinarith [h_eq, h8, h6, h7, Real.sin_pos_of_pos_of_lt_pi (show 0 < 3 * θ by linarith [h_pos, Real.pi_pos, h3] ) (show 3 * θ < Real.pi by linarith [Real.pi_pos, h3, h_pos] ), Real.sin_pos_of_pos_of_lt_pi (show 0 < 3 * (π / 20) by linarith [Real.pi_pos] ) (show 3 * (π / 20) < Real.pi by linarith [Real.pi_pos] ), Real.sin_pos_of_pos_of_lt_pi (show 0 < 7 * θ by linarith [h_pos, Real.pi_pos, h3] ) (show 7 * θ < Real.pi by linarith [Real.pi_pos, h3, h_pos] ), Real.sin_pos_of_pos_of_lt_pi (show 0 < 7 * (π / 20) by linarith [Real.pi_pos] ) (show 7 * (π / 20) < Real.pi by linarith [Real.pi_pos] ), Real.pi_pos ]