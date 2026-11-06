import Mathlib

open Real

theorem inequalities_109120 (x : ℝ) (hx : x ≠ 0) :
    (x > 0 → x + 1 / x ≥ 2 ∧ (x + 1 / x = 2 ↔ x = 1)) ∧
    (x < 0 → x + 1 / x ≤ -2 ∧ (x + 1 / x = -2 ↔ x = -1)) := by
  constructor
  · -- Assume x > 0
    intro h
    have h1 : x + 1 / x - 2 ≥ 0 := by
      have h2 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := by 
        field_simp
        ring
      rw [h2]
      have h3 : x ^ 2 + 1 - 2 * x = (x - 1) ^ 2 := by
        ring
      have h4 : (x ^ 2 + 1 - 2 * x) ≥ 0 := by
        rw [h3]
        exact sq_nonneg (x - 1)
      apply div_nonneg
      · -- Show numerator ≥ 0
        linarith
      · -- Show denominator ≥ 0 (since x > 0)
        linarith
    have hge : x + 1 / x ≥ 2 := by
      linarith
    constructor
    · exact hge
    · -- Proof of the iff condition (x + 1 / x = 2 ↔ x = 1)
      constructor
      · -- Forward implication: If x + 1 / x = 2, then x = 1
        intro h_eq
        have h2 : x ^ 2 + 1 - 2 * x = 0 := by
          have h3 : x + 1 / x - 2 = 0 := by
            linarith
          have h4 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := by 
            field_simp
            ring
          rw [h4] at h3
          have h5 : x ≠ 0 := hx
          field_simp at h3 ⊢
          nlinarith
        have h2' : (x - 1) ^ 2 = 0 := by
          nlinarith
        have h3 : x - 1 = 0 := by
          apply pow_eq_zero 
          exact h2'
        linarith
      · -- Backward implication: If x = 1, then x + 1 / x = 2
        intro h_eq
        rw [h_eq]
        norm_num
  · -- Assume x < 0
    intro h
    have h1 : x + 1 / x + 2 ≤ 0 := by
      have h2 : x + 1 / x + 2 = (x ^ 2 + 1 + 2 * x) / x := by 
        field_simp
        ring
      rw [h2]
      have h3 : x ^ 2 + 1 + 2 * x = (x + 1) ^ 2 := by
        ring
      have h4 : (x ^ 2 + 1 + 2 * x) ≥ 0 := by
        rw [h3]
        exact sq_nonneg (x + 1)
      have h5 : (x ^ 2 + 1 + 2 * x) / x ≤ 0 := by
        apply div_nonpos_of_nonneg_of_nonpos
        · linarith
        all_goals linarith
      linarith
    have hle : x + 1 / x ≤ -2 := by
      linarith
    constructor
    · exact hle
    · -- Proof of the iff condition (x + 1 / x = -2 ↔ x = -1)
      constructor
      · -- Forward implication: If x + 1 / x = -2, then x = -1
        intro h_eq
        have h2 : x ^ 2 + 1 + 2 * x = 0 := by
          have h3 : x + 1 / x + 2 = 0 := by
            linarith
          have h4 : x + 1 / x + 2 = (x ^ 2 + 1 + 2 * x) / x := by 
            field_simp
            ring
          rw [h4] at h3
          have h5 : x ≠ 0 := hx
          field_simp at h3 ⊢
          nlinarith
        have h2' : (x + 1) ^ 2 = 0 := by
          nlinarith
        have h3 : x + 1 = 0 := by
          apply pow_eq_zero 
          exact h2'
        linarith
      · -- Backward implication: If x = -1, then x + 1 / x = -2
        intro h_eq
        rw [h_eq]
        norm_num