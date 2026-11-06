import Mathlib

open Real

theorem inequalities_186698 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 1 / a + 1 / b = 2) :
    a + b ≥ 2 ∧
    (a + b = 2 ↔ a = b) := by
  have h1 : a + b = 2 * a * b := by
    field_simp at h
    nlinarith
  have h2 : a + b ≥ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), mul_pos ha hb]
  have h3 : a + b = 2 ↔ a = b := by
    constructor
    · -- Assume a + b = 2, prove a = b
      intro heq
      have h4 : a * b = 1 := by
        nlinarith [h1, heq]
      have h5 : (a - 1) * (b - 1) = 0 := by
        nlinarith [h4, heq]
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- Assume a - 1 = 0
        have h8 : a = 1 := by
          linarith
        linarith
      · -- Assume b - 1 = 0
        have h9 : b = 1 := by
          linarith
        linarith
    · -- Assume a = b, prove a + b = 2
      intro heq
      have h4 : b = a := by
        linarith [heq]
      rw [h4] at h1
      have ha1 : a = 1 := by
        nlinarith [sq_nonneg (a - 1), sq_pos_of_pos ha]
      nlinarith [ha1]
  constructor
  · exact h2
  · exact h3