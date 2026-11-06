import Mathlib

theorem inequalities_83446 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a * b * c = 1) (hinv : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b < 1 ∧ c < 1) ∨ (b > 1 ∧ a < 1 ∧ c < 1) ∨ (c > 1 ∧ a < 1 ∧ b < 1) := by

  have h1 : (1 / a + 1 / b + 1 / c) = (b * c + a * c + a * b) := by
    have h2 : 1 / a = b * c := by
      have h5 : a * b * c = 1 := hsum
      have h6 : a ≠ 0 := by linarith
      field_simp [h6]
      <;> nlinarith
    have h3 : 1 / b = a * c := by
      have h5 : a * b * c = 1 := hsum
      have h7 : b ≠ 0 := by linarith
      field_simp [h7]
      <;> nlinarith
    have h4 : 1 / c = a * b := by
      have h5 : a * b * c = 1 := hsum
      have h8 : c ≠ 0 := by linarith
      field_simp [h8]
      <;> nlinarith
    linarith [h2, h3, h4]
  rw [h1] at hinv
  
  by_cases ha1 : a > 1
  · -- Assume a > 1, need to prove (a > 1 ∧ b < 1 ∧ c < 1) ∨ (b > 1 ∧ a < 1 ∧ c < 1) ∨ (c > 1 ∧ a < 1 ∧ b < 1)
    left
    constructor
    · exact ha1
    constructor
    · -- Show b < 1
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    · -- Show c < 1
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  
  by_cases hb1 : b > 1
  · -- Assume b > 1, need to prove ..., or ...
    right
    left
    constructor
    · exact hb1
    constructor
    · -- Show a < 1
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    · -- Show c < 1
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

  have h5 : c > 1 := by
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  right
  right
  constructor
  · -- Show c > 1
    exact h5
  constructor
  · -- Show a < 1
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  · -- Show b < 1
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]