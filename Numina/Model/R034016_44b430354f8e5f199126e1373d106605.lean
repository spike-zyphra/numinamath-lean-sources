import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_296286 (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (h : a + b = 2) :
  1 ≤ 1 / (1 + a ^ n) + 1 / (1 + b ^ n) := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : a + b = 2 := h
  have h4 : a * b ≤ 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), h3]

  -- Show that $(a^n \cdot b^n) \leq 1$
  have h5 : a ^ n * b ^ n ≤ 1 := by
    have h6 : a * b ≤ 1 := h4
    have h7 : a ^ n * b ^ n = (a * b) ^ n := by
      rw [mul_pow]
    rw [h7]
    have h8 : (a * b) ^ n ≤ (1 : ℝ) ^ n := by
      apply pow_le_pow_left
      all_goals
        nlinarith [h6]
    have h9 : (1 : ℝ) ^ n = 1 := by
      simp
    linarith [h8, h9]

  have h7 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) ) - 1 ≥ 0 := by
    have h8 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) ) - 1 =
      ( (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) ) / ((1 + a ^ n) * (1 + b ^ n)) := by
      field_simp
      <;> ring
    rw [h8]
    have h9 : ( (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) ) ≥ 0 := by
      have h10 : ( (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) ) = 1 - (a ^ n * b ^ n) := by
        ring_nf
      rw [h10]
      nlinarith [h5]

    have h10 : ( (1 + a ^ n) * (1 + b ^ n) ) > 0 := by
      positivity
    apply div_nonneg
    linarith
    linarith
  linarith