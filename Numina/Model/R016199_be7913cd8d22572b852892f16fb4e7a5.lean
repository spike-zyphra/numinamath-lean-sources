import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_120802 : sin (4 : ℝ) < sin (3 : ℝ) ∧ sin (3 : ℝ) < sin (1 : ℝ) ∧ sin (1 : ℝ) < sin (2 : ℝ) := by

  have h1 : sin (4 : ℝ) < 0 := by
    have h1 : Real.pi < (4 : ℝ) := by linarith [Real.pi_lt_31416, Real.pi_gt_31415]
    have h4 : sin (4 : ℝ) = -sin (4 - Real.pi : ℝ) := by
      rw [show (4 : ℝ) = Real.pi + (4 - Real.pi) by ring]
      rw [sin_add, sin_pi, cos_pi]
      ring
    have h5 : 0 < (4 - Real.pi : ℝ) := by linarith [Real.pi_lt_31416, Real.pi_gt_31415]
    have h6 : sin (4 - Real.pi : ℝ) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_lt_31416, Real.pi_gt_31415]
    linarith [h4, h6]

  have h2 : sin (3 : ℝ) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [Real.pi_lt_31416, Real.pi_gt_31415]

  have h3 : sin (3 : ℝ) < sin (1 : ℝ) := by
    have h4 : sin (3 : ℝ) = sin (Real.pi - (3 : ℝ)) := by
      rw [show Real.pi - (3 : ℝ) = Real.pi - 3 by ring]
      rw [sin_pi_sub]
    have h5 : Real.pi - (3 : ℝ) < (1 : ℝ) := by
      nlinarith [Real.pi_lt_31416, Real.pi_gt_31415]
    have h6 : sin (Real.pi - (3 : ℝ)) < sin (1 : ℝ) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        nlinarith [Real.pi_lt_31416, Real.pi_gt_31415, Real.pi_pos]
    linarith [h4, h6]

  have h4 : sin (1 : ℝ) < sin (2 : ℝ) := by
    have h7 : sin (2 : ℝ) = sin (Real.pi - (2 : ℝ)) := by
      rw [show Real.pi - (2 : ℝ) = Real.pi - 2 by ring]
      rw [sin_pi_sub]
    have h8 : (1 : ℝ) < Real.pi - (2 : ℝ) := by
      nlinarith [Real.pi_lt_31416, Real.pi_gt_31415]
    have h9 : sin (1 : ℝ) < sin (Real.pi - (2 : ℝ)) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        nlinarith [Real.pi_lt_31416, Real.pi_gt_31415, Real.pi_pos]
    linarith [h7, h9]

  constructor
  · -- Show that $\sin 4 < \sin 3$
    linarith [h1, h2]
  constructor
  · -- Show that $\sin 3 < \sin 1$
    exact h3
  · -- Show that $\sin 1 < \sin 2$
    exact h4