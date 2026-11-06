import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_11397 : IsLeast {z : ℝ | 0 < z ∧ ∃ x, cos x = 0 ∧ cos (x + z) = 1 / 2} (π / 6) := by
  constructor
  · -- Show π/6 is in the set
    constructor
    · -- Show π/6 > 0
      linarith [Real.pi_pos]
    · -- Show ∃ x, cos x = 0 ∧ cos (x + π / 6) = 1 / 2
      use (3 * Real.pi / 2)
      constructor
      · -- Show cos (3 * π / 2) = 0
        have h1 : cos (3 * Real.pi / 2) = 0 := by
          have h1 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by
            ring
          rw [h1]
          rw [cos_add, cos_pi, sin_pi]
          norm_num
        exact h1
      · -- Show cos (3 * π / 2 + π / 6) = 1 / 2
        have h2 : cos (3 * Real.pi / 2 + Real.pi / 6) = 1 / 2 := by
          have h3 : 3 * Real.pi / 2 + Real.pi / 6 = 5 * Real.pi / 3 := by
            linarith [Real.pi_pos]
          rw [h3]
          have h4 : cos (5 * Real.pi / 3) = cos (Real.pi / 3) := by
            have h5 : 5 * Real.pi / 3 = 2 * Real.pi - (Real.pi / 3) := by
              linarith [Real.pi_pos]
            rw [h5]
            rw [cos_two_pi_sub]
          rw [h4]
          have h5 : cos (Real.pi / 3) = 1 / 2 := by
            exact cos_pi_div_three
          rw [h5]
        exact h2
  · -- Show that π/6 is the minimum
    intro z hz
    rcases hz with ⟨hz_pos, x, hx1, hx2⟩
    by_contra h
    push_neg at h
    have h1 : cos x = 0 := hx1
    have h2 : cos (x + z) = 1 / 2 := hx2
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    rw [h1] at h3
    have h4 : sin x ^ 2 = 1 := by nlinarith
    have h5 : sin x = 1 ∨ sin x = -1 := by
      have h8 : sin x ^ 2 = 1 := h4
      have : sin x = 1 ∨ sin x = -1 := by
        rw [sq_eq_one_iff] at h8
        tauto
      assumption
    have h6 : cos (x + z) = cos x * cos z - sin x * sin z := by
      rw [cos_add]
    rw [h1] at h6
    rw [h6] at h2
    have h7 : sin z > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hz_pos, h]
      linarith [hz_pos, h, Real.pi_gt_three]
    rcases h5 with (h5 | h5)
    · -- case h5, sin x = 1
      have h8 : sin z = -1 / 2 := by
        rw [h5] at h2
        nlinarith
      nlinarith [show sin z > 0 by nlinarith]
    · -- case h5, sin x = -1
      have h9 : sin z = 1 / 2 := by
        rw [h5] at h2
        nlinarith
      have h8 : sin z < 1 / 2 := by
        have h10 : z < Real.pi / 6 := h
        have h11 : sin z < sin (Real.pi / 6) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            linarith [Real.pi_pos, h10]
        have h12 : sin (Real.pi / 6) = 1 / 2 := by
          exact sin_pi_div_six
        linarith [h12, h11]
      nlinarith