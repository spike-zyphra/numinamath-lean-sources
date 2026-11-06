import Mathlib

open Real Set
open scoped Real

theorem calculus_22358 : arcsin (sin 3) + arcsin (sin 4) + arcsin (sin 5) = -2 := by
  have h1 : arcsin (sin 3) = Real.pi - 3 := by
    have h2 : arcsin (sin 3) = Real.pi - 3 := by
      have h2 : -(Real.pi / 2) ≤ Real.pi - 3 := by
        nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      have h3 : Real.pi - 3 ≤ Real.pi / 2 := by
        nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      have h4 : arcsin (sin 3) = Real.pi - 3 := by
        have h5 : sin 3 = sin (Real.pi - 3) := by
          rw [sin_pi_sub]
        rw [h5]
        have h6 : arcsin (sin (Real.pi - 3)) = Real.pi - 3 := by
          apply arcsin_sin
          all_goals linarith [Real.pi_gt_31415, Real.pi_lt_31416]
        exact h6
      exact h4
    exact h2
  -- Compute arcsin(sin 4) = π - 4
  have h2 : arcsin (sin 4) = Real.pi - 4 := by
    have h1 : arcsin (sin 4) = Real.pi - 4 := by
      have h2 : -(Real.pi / 2) ≤ Real.pi - 4 := by
        nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      have h3 : Real.pi - 4 ≤ Real.pi / 2 := by
        nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      have h4 : arcsin (sin 4) = Real.pi - 4 := by
        have h5 : sin 4 = sin (Real.pi - 4) := by
          rw [sin_pi_sub]
        rw [h5]
        have h6 : arcsin (sin (Real.pi - 4)) = Real.pi - 4 := by
          apply arcsin_sin
          all_goals linarith [Real.pi_gt_31415, Real.pi_lt_31416]
        exact h6
      exact h4
    exact h1
  have h3 : arcsin (sin 5) = 5 - 2 * Real.pi := by
    have h7 : arcsin (sin 5) = 5 - 2 * Real.pi := by
      have h21 : -(Real.pi / 2) ≤ 5 - 2 * Real.pi := by
        nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      have h22 : 5 - 2 * Real.pi ≤ Real.pi / 2 := by
        nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      have h8 : sin 5 = sin (5 - 2 * Real.pi) := by
        have h9 : sin (5 - 2 * Real.pi) = sin 5 := by
          rw [show 5 - 2 * Real.pi = 5 - (2 * Real.pi) by ring]
          rw [sin_sub, sin_two_pi, cos_two_pi]
          simp
        linarith [h9]
      rw [h8]
      have h10 : arcsin (sin (5 - 2 * Real.pi)) = 5 - 2 * Real.pi := by
        apply arcsin_sin
        all_goals nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      exact h10
    exact h7
  rw [h1, h2, h3]
  nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]