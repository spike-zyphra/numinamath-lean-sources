import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_253726 (x : ℝ) (hx : x ≠ 0) :
    (|2 * x - 3| ≤ 3 ∧ 1 / x < 1) ↔ (1 < x ∧ x ≤ 3) := by
  constructor
  · -- Assume (|2 * x - 3| ≤ 3 ∧ 1 / x < 1), prove (1 < x ∧ x ≤ 3)
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : -3 ≤ 2 * x - 3 := by
      linarith [abs_le.mp h1]
    have h4 : 2 * x - 3 ≤ 3 := by
      linarith [abs_le.mp h1]
    have h5 : 0 ≤ x := by
      linarith
    have h6 : x ≤ 3 := by
      linarith
    by_cases h8 : x > 0
    · -- If x > 0, then multiplying both sides of 1/x < 1 by x gives 1 < x
      have h9 : 1 < x := by
        have h10 : 1 / x < 1 := h2
        have h11 : 1 / x * x < (1 : ℝ) * x := by
          apply mul_lt_mul_of_pos_right
          linarith
          linarith
        have h12 : (1 / x * x) = 1 := by
          field_simp [hx]
        linarith [h12, h11]
      constructor
      · -- Show 1 < x
        linarith
      · -- Show x ≤ 3
        linarith
    · -- If x ≤ 0, since x ≠ 0, then x < 0
      have h9 : x < (0 : ℝ) := by
        by_contra h
        push_neg at h
        have : x = 0 := by linarith
        contradiction
      have h10 : x < 0 := h9
      have h11 : 0 ≤ x := by
        linarith
      linarith
  · -- Assume (1 < x ∧ x ≤ 3), prove (|2 * x - 3| ≤ 3 ∧ 1 / x < 1)
    intro h
    rcases h with ⟨h1, h2⟩
    constructor
    · -- Show |2 * x - 3| ≤ 3
      have h3 : -3 ≤ 2 * x - 3 := by
        linarith
      have h4 : 2 * x - 3 ≤ 3 := by
        linarith
      apply abs_le.mpr
      constructor <;> linarith
    · -- Show 1 / x < 1
      have h8 : x > 0 := by
        linarith
      have h9 : 1 / x < 1 := by
        have h10 : 1 < x := h1
        have h11 : 1 < (x : ℝ) := h1
        have h13 : (1 / x : ℝ) < (1 : ℝ) := by
          have h14 : 1 / x < (1 : ℝ) := by
            apply (div_lt_iff₀ (by linarith)).mpr
            nlinarith
          linarith
        linarith
      exact h9