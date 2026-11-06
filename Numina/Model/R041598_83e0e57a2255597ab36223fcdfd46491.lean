import Mathlib

open Real

theorem inequalities_131102 (x : ℝ) (hx : 0 < x) :
    0 ≤ x ∧ x ≤ 1 / x ∧ 1 / x ≤ 1 ↔ x = 1 := by
  constructor
  · -- Assume the inequalities hold, prove x = 1
    rintro ⟨h1, h2, h3⟩
    have h4 : 0 < x := hx
    have h5 : x * x ≤ 1 := by
      have h6 : x ≤ 1 / x := h2
      have h7 : x * x ≤ 1 := by
        have h8 : x ≤ 1 / x := h6
        have h9 : x * x ≤ x * (1 / x) := by
          apply mul_le_mul_of_nonneg_left h8
          linarith
        have h10 : x * (1 / x) = 1 := by
          field_simp
        nlinarith [h10]
      linarith
    have h6 : 1 ≤ x := by
      have h7 : 1 / x ≤ 1 := h3
      have h8 : 0 < x := h4
      have h9 : 1 / x * x ≤ (1 : ℝ) * x := by 
        have h10 : (1 / x) ≤ (1 : ℝ) := h7 
        have h11 : (1 / x) * x ≤ (1 : ℝ) * x := by 
          apply mul_le_mul_of_nonneg_right h10 
          linarith
        linarith
      have h10 : (1 / x) * x = 1 := by 
        field_simp
      linarith [h9, h10]
    have h7 : x = 1 := by 
      nlinarith [h5, h6, show 0 < x by linarith]
    exact h7
  · -- Assume x = 1, prove the inequalities
    intro h
    rw [h]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num