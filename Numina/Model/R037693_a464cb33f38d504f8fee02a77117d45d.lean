import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_603106 (x : ℝ) (hx : x ≠ -1) :
    (2 * x - 1) / abs (x + 1) ≤ 0 ↔ x < -1 ∨ -1 < x ∧ x ≤ 1 / 2 := by
  constructor
  · -- Forward implication: (2 * x - 1) / abs (x + 1) ≤ 0 implies x < -1 ∨ -1 < x ∧ x ≤ 1 / 2
    intro h
    by_cases h1 : x + 1 > 0
    · -- x + 1 > 0, so |x + 1| = x + 1 > 0
      have h2 : abs (x + 1) = x + 1 := by
        rw [abs_of_pos h1]
      have h3 : 2 * x - 1 ≤ 0 := by
        have pos1 : abs (x + 1) > 0 := by
          rw [h2]
          linarith
        apply (div_nonpos_iff).mp at h
        cases h with
        | inl h1 =>
          nlinarith
        | inr h2 =>
          nlinarith
      have hx2 : x ≤ 1 / 2 := by linarith
      right
      constructor
      · -- Show that -1 < x
        linarith
      · -- Show that x ≤ 1 / 2
        linarith
    · -- x + 1 ≤ 0
      have h1' : x + 1 < 0 := by
        by_contra h2
        push_neg at h2
        have h3 : x + 1 = 0 := by linarith
        have h4 : x = -1 := by linarith
        tauto
      -- x + 1 < 0, so |x + 1| = -(x + 1) > 0
      have h2 : abs (x + 1) = -(x + 1) := by
        rw [abs_of_neg h1']
      have h3 : 2 * x - 1 ≤ 0 := by
        have pos1 : abs (x + 1) > 0 := by
          rw [h2]
          linarith
        apply (div_nonpos_iff).mp at h
        cases h with
        | inl h1 =>
          nlinarith
        | inr h2 =>
          nlinarith
      left
      linarith
  · -- Backward implication: x < -1 ∨ -1 < x ∧ x ≤ 1 / 2 implies (2 * x - 1) / abs (x + 1) ≤ 0
    intro h
    cases h with
    | inl h1 =>
      -- x < -1
      have h1' : x + 1 < 0 := by linarith
      have h2 : abs (x + 1) = -(x + 1) := by
        rw [abs_of_neg h1']
      have pos1 : abs (x + 1) > 0 := by
        rw [h2]
        linarith
      have h4 : 2 * x - 1 ≤ 0 := by linarith
      rw [h2]
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · linarith
      all_goals nlinarith
    | inr h2 =>
      -- -1 < x ∧ x ≤ 1 / 2
      -- x > -1
      have h1 : x + 1 > 0 := by linarith
      have h2' : abs (x + 1) = x + 1 := by
        rw [abs_of_pos h1]
      have pos1 : abs (x + 1) > 0 := by
        rw [h2']
        linarith
      have h4 : 2 * x - 1 ≤ 0 := by linarith
      rw [h2']
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · linarith
      all_goals nlinarith