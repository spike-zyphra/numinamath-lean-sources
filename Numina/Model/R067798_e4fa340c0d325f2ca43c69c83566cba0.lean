import Mathlib

theorem algebra_261021 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + b = c + d) (h2 : a * d = b * c) (h3 : a * c + b * d = 1) :
    a + b + c + d ≤ 2 * Real.sqrt 2 := by
  have h4 : a + b + c + d = 2 * (a + b) := by
    linarith [h1]
  have h5 : a = c := by
    nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), h1, h2, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
  have h6 : b = d := by
    nlinarith [h1, h5]
  have h7 : a * c + b * d = a ^ 2 + b ^ 2 := by
    rw [show c = a by linarith [h5], show d = b by linarith [h6]]
    all_goals nlinarith
  have h8 : a ^ 2 + b ^ 2 = 1 := by
    linarith [h3, h7]
  have h9 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have h10 : (a + b) ^ 2 ≤ 2 := by
    have h11 : a ^ 2 + b ^ 2 = 1 := h8
    nlinarith
  have h12 : a + b ≤ Real.sqrt 2 := by
    have h13 : (a + b) ^ 2 ≤ (2 : ℝ) := h10
    have h14 : 0 ≤ (a + b : ℝ) := by nlinarith
    have h15 : Real.sqrt ((a + b) ^ 2) = a + b := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg h14]
    have h16 : Real.sqrt ((a + b) ^ 2) ≤ Real.sqrt (2 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    linarith [h15, h16]
  have h17 : a + b + c + d = 2 * (a + b) := by
    linarith [h4, h5, h6]
  linarith [h17, h12]