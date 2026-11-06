import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_208058 : IsLeast {y : ℝ | ∃ x, y = sin (x + 3) - sin (x + 1) - 2 * cos (x + 2)} (2 * (sin 1 - 1)) := by
  constructor
  · -- First part: existence.
    use -2
    have h1 : sin (-2 + 3) = sin 1 := by
      ring_nf
    have h2 : sin (-2 + 1) = -sin 1 := by
      have h21 : sin (-2 + 1) = sin (-1) := by ring_nf
      rw [h21]
      have h22 : sin (-1) = -sin 1 := by
        rw [show (-1 : ℝ) = - (1 : ℝ) by ring]
        rw [sin_neg]
      rw [h22]
    have h3 : cos (-2 + 2) = 1 := by
      have h31 : cos (-2 + 2) = cos (0 : ℝ) := by
        ring_nf
      rw [h31]
      norm_num [cos_zero]
    rw [h1, h2, h3]
    ring_nf
  · -- Let y be an element of the set, show y >= 2 * (sin 1 - 1)
    intro y
    rintro ⟨x, hx⟩
    have h4 : sin (x + 3) = sin (x + 2) * cos 1 + cos (x + 2) * sin 1 := by
      have : x + 3 = (x + 2) + 1 := by ring
      rw [this]
      rw [sin_add]
    have h5 : sin (x + 1) = sin (x + 2) * cos 1 - cos (x + 2) * sin 1 := by
      have : x + 1 = (x + 2) - 1 := by ring
      rw [this]
      rw [sin_sub]
      <;> ring_nf
    rw [h4, h5] at hx
    have h6 : (sin (x + 2) * cos 1 + cos (x + 2) * sin 1) - (sin (x + 2) * cos 1 - cos (x + 2) * sin 1) = 2 * cos (x + 2) * sin 1 := by
      ring_nf
    rw [h6] at hx
    have h7 : 2 * cos (x + 2) * sin 1 - 2 * cos (x + 2) = 2 * cos (x + 2) * (sin 1 - 1) := by
      ring_nf
    rw [h7] at hx
    have h9 : sin 1 < 1 := by
      have h3 : sin 1 < sin (Real.pi / 2) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          try linarith [Real.pi_gt_three, Real.pi_lt_31416]
      have h4 : sin (Real.pi / 2) = 1 := by
        rw [sin_pi_div_two]
      linarith [h3, h4]
    have h11 : 2 * cos (x + 2) * (sin 1 - 1) ≥ 2 * (sin 1 - 1) := by
      have h13 : cos (x + 2) ≤ 1 := by
        have h14 : cos (x + 2) ≤ 1 := by
          apply cos_le_one
        linarith
      have h14 : sin 1 - 1 < 0 := by
        linarith [h9]
      nlinarith [sq_nonneg (cos (x + 2) - 1), sq_nonneg (sin 1 - 1), Real.sin_sq_add_cos_sq 1, Real.sin_le_one 1, Real.sin_le_one (x + 2), Real.cos_le_one (x + 2)]
    linarith [hx, h11]