import Mathlib

open Real

theorem inequalities_256447 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a ≤ 1) (h2 : b ≤ 1) :
    (a + b) / (1 + a * b) ≤ 1 / (1 + a) + 1 / (1 + b) ∧ ((a + b) / (1 + a * b) = 1 / (1 + a) + 1 / (1 + b) ↔ (a = 1 ∧ b = 1)) := by

  constructor
  · -- Prove the inequality
    have h3 : 0 < 1 + a * b := by
      nlinarith
    have h4 : 0 < 1 + a := by
      nlinarith
    have h5 : 0 < 1 + b := by
      nlinarith
    have h6 : (a + b) / (1 + a * b) - (1 / (1 + a) + 1 / (1 + b)) ≤ 0 := by
      have h7 : (a + b) / (1 + a * b) - (1 / (1 + a) + 1 / (1 + b)) =
          ((a + b) * (1 + a) * (1 + b) - (1 + b) * (1 + a * b) - (1 + a) * (1 + a * b)) / ((1 + a * b) * (1 + a) * (1 + b)) := by
        field_simp
        <;> ring
      rw [h7]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is non-positive
        have h8 : (a + b) * (1 + a) * (1 + b) - (1 + b) * (1 + a * b) - (1 + a) * (1 + a * b) ≤ 0 := by
          nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
        linarith
      · -- Show the denominator is non-negative
        positivity
    linarith
  · -- Prove the equality condition
    constructor
    · -- Forward implication: if equality holds, then a = 1 and b = 1
      intro heq
      have h3 : 0 < 1 + a * b := by
        nlinarith
      have h4 : 0 < 1 + a := by
        nlinarith
      have h5 : 0 < 1 + b := by
        nlinarith
      have heq1 : (a + b) / (1 + a * b) - (1 / (1 + a) + 1 / (1 + b)) = 0 := by
        linarith
      have h7 : (a + b) / (1 + a * b) - (1 / (1 + a) + 1 / (1 + b)) =
          ((a + b) * (1 + a) * (1 + b) - (1 + b) * (1 + a * b) - (1 + a) * (1 + a * b)) / ((1 + a * b) * (1 + a) * (1 + b)) := by
        field_simp
        <;> ring
      rw [h7] at heq1
      have heq2 : (a + b) * (1 + a) * (1 + b) - (1 + b) * (1 + a * b) - (1 + a) * (1 + a * b) = 0 := by
        field_simp at heq1 ⊢
        nlinarith
      have h8 : (a - 1) ^ 2 + (b - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), mul_pos ha hb]
      have ha1 : a - 1 = 0 := by nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1)]
      have hb1 : b - 1 = 0 := by nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1)]
      constructor
      · linarith
      · linarith
    · -- Backward implication: if a = 1 and b = 1, then equality holds
      rintro ⟨ra, rb⟩
      rw [ra, rb]
      norm_num