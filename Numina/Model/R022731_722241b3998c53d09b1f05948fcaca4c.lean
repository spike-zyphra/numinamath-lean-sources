import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_327560 (x : ℝ) (hx : 2*x - abs (x-1) ≠ 0) :
    (x+1)/(2*x - abs (x-1)) ≥ 1 ↔ x > 1/3 := by
  constructor
  · -- Forward implication: (x+1)/(2*x - abs (x-1)) ≥ 1 implies x > 1/3
    intro h
    by_cases h1 : x - 1 ≥ 0
    · -- If x ≥ 1, then |x-1| = x-1
      have h2 : abs (x - 1) = x - 1 := abs_of_nonneg h1
      have h3 : 2 * x - abs (x - 1) = x + 1 := by
        rw [h2]
        linarith
      rw [h3] at h
      have h4 : x ≥ 1 := by linarith
      linarith
    · -- If x < 1, then |x-1| = 1-x
      have h2 : abs (x - 1) = 1 - x := by
        rw [abs_of_neg (show x - 1 < 0 by linarith)]
        all_goals
          linarith
      have h3 : 2 * x - abs (x - 1) = 3 * x - 1 := by
        rw [h2]
        linarith
      rw [h3] at h
      have h4 : x < 1 := by linarith
      by_cases h6 : 3 * x - 1 > 0
      · -- If 3x - 1 > 0, then x > 1/3
        have h7 : x > 1/3 := by linarith
        linarith
      · -- If 3x - 1 ≤ 0
        have h7 : 3 * x - 1 ≤ 0 := by linarith
        have h12 : (3 * x - 1) < 0 := by
          by_contra h9
          push_neg at h9
          have h0 : 3 * x - 1 = 0 := by linarith
          have h00 : 2 * x - abs (x-1) = 0 := by linarith [h2, h0]
          contradiction
        have h12 : (x + 1) / (3 * x - 1) ≥ 1 := h
        apply (le_div_iff_of_neg' (show 3 * x - 1 < 0 by linarith)).mp at h12
        linarith
  · -- Backward implication: x > 1/3 implies (x+1)/(2*x - abs (x-1)) ≥ 1
    intro h
    by_cases h1 : x - 1 ≥ 0
    · -- If x ≥ 1, then |x-1| = x-1
      have h2 : abs (x - 1) = x - 1 := abs_of_nonneg h1
      have h3 : 2 * x - abs (x - 1) = x + 1 := by
        rw [h2]
        linarith
      rw [h3]
      have h4 : x ≥ 1 := by linarith
      have h5 : (x + 1) / (x + 1) ≥ 1 := by
        apply (le_div_iff₀ (by linarith)).mpr
        all_goals
          nlinarith
      linarith
    · -- If x < 1, then |x-1| = 1-x
      have h2 : abs (x - 1) = 1 - x := by
        rw [abs_of_neg (show x - 1 < 0 by linarith)]
        all_goals
          linarith
      have h3 : 2 * x - abs (x - 1) = 3 * x - 1 := by
        rw [h2]
        linarith
      rw [h3]
      have h4 : x < 1 := by linarith
      have h5 : 3 * x - 1 > 0 := by linarith
      have h7 : (x + 1) / (3 * x - 1) ≥ 1 := by
        apply (le_div_iff₀ (show 0 < 3 * x - 1 by linarith)).mpr
        linarith
      linarith