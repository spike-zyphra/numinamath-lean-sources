import Mathlib

open Real Set

theorem inequalities_227068 (n : ℕ) (hn : n > 0) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    1 ≤ 1 / (1 + a ^ n) + 1 / (1 + b ^ n) := by
  have h1 : 0 < a ^ n := by positivity
  have h2 : 0 < b ^ n := by positivity
  have h4 : a * b ≤ 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), h]
  have h8 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1) ≥ 0 := by
    have h7 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1) = (1 - (a * b) ^ n) / ((1 + a ^ n) * (1 + b ^ n)) := by
      field_simp
      ring
    rw [h7]
    have h5 : (a * b) ^ n ≤ (1 : ℝ) := by
      have h6 : (a * b) ≤ (1 : ℝ) := by nlinarith
      have h7 : (a * b) ^ n ≤ (1 : ℝ) ^ n := by
        apply pow_le_pow_left
        all_goals nlinarith
      have h8 : (1 : ℝ) ^ n = (1 : ℝ) := by
        simp
      linarith
    have h9 : 1 - (a * b) ^ n ≥ 0 := by
      nlinarith [h5]
    apply div_nonneg
    linarith
    positivity
  linarith