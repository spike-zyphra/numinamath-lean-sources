import Mathlib

open Real Set

theorem inequalities_206727 (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    1 / (1 + a ^ n) + 1 / (1 + b ^ n) ≥ 1 := by
  have h1 : b = 2 - a := by linarith
  have h2 : a > 0 := by linarith
  have h3 : b > 0 := by linarith
  have h4 : 0 < a ^ n := by positivity
  have h5 : 0 < b ^ n := by positivity
  have h6 : a * b ≤ 1 := by 
    nlinarith [sq_nonneg (a - 1), h]
  have h7 : a ^ n * b ^ n ≤ 1 := by
    have h8 : a * b ≤ 1 := h6
    have h9 : a ^ n * b ^ n = (a * b) ^ n := by
      rw [mul_pow]
    rw [h9]
    have h10 : a * b > 0 := by positivity
    have h11 : (a * b) ^ n ≤ (1 : ℝ) := by
      have h12 : a * b ≤ (1 : ℝ) := h8
      have h13 : a * b ≥ 0 := by positivity
      have h14 : (a * b) ^ n ≤ (1 : ℝ) ^ n := by
        apply pow_le_pow_left
        all_goals nlinarith
      have h15 : (1 : ℝ) ^ n = 1 := by
        norm_num
      linarith
    linarith
  have h8 : 1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1 ≥ 0 := by
    have h9 : 0 < (1 + a ^ n) * (1 + b ^ n) := by positivity
    have h10 : 1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1 = (1 - (a ^ n * b ^ n)) / ((1 + a ^ n) * (1 + b ^ n)) := by
      field_simp
      <;> ring_nf <;> nlinarith
    rw [h10]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith