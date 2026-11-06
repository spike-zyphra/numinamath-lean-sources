import Mathlib

open Real

theorem inequalities_155399 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    3 < sqrt (1 - a^2) + sqrt (1 - b^2) + sqrt (1 - c^2) + a + b + c := by

  have ha1 : a < 1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have hb1 : b < 1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have hc1 : c < 1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h1 : sqrt (1 - a^2) + a > 1 := by
    have ha2 : a < 1 := ha1
    have ha3 : 0 < 1 - a := by nlinarith
    have h11 : sqrt (1 - a^2) > 1 - a := by
      have h12 : (1 - a) < sqrt (1 - a^2) := by
        have h13 : (1 - a) ^ 2 < 1 - a ^ 2 := by
          nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2)]
        have h14 : (1 - a) ^ 2 < (sqrt (1 - a^2)) ^ 2 := by
          linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 - a ^ 2 by nlinarith)]
        have h15 : (1 - a) ≥ 0 := by nlinarith
        have h16 : sqrt (1 - a^2) ≥ 0 := by apply Real.sqrt_nonneg
        nlinarith [Real.sqrt_nonneg (1 - a^2)]
      linarith
    linarith

  have h2 : sqrt (1 - b^2) + b > 1 := by
    have hb2 : b < 1 := hb1
    have hb3 : 0 < 1 - b := by nlinarith
    have h21 : sqrt (1 - b^2) > 1 - b := by
      have h22 : (1 - b) < sqrt (1 - b^2) := by
        have h23 : (1 - b) ^ 2 < 1 - b ^ 2 := by
          nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2)]
        have h24 : (1 - b) ^ 2 < (sqrt (1 - b^2)) ^ 2 := by
          linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 - b ^ 2 by nlinarith)]
        have h25 : (1 - b) ≥ 0 := by nlinarith
        have h26 : sqrt (1 - b^2) ≥ 0 := by apply Real.sqrt_nonneg
        nlinarith [Real.sqrt_nonneg (1 - b^2)]
      linarith
    linarith

  have h3 : sqrt (1 - c^2) + c > 1 := by
    have hc2 : c < 1 := hc1
    have hc3 : 0 < 1 - c := by nlinarith
    have h31 : sqrt (1 - c^2) > 1 - c := by
      have h32 : (1 - c) < sqrt (1 - c^2) := by
        have h33 : (1 - c) ^ 2 < 1 - c ^ 2 := by
          nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2)]
        have h34 : (1 - c) ^ 2 < (sqrt (1 - c^2)) ^ 2 := by
          linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 - c ^ 2 by nlinarith)]
        have h35 : (1 - c) ≥ 0 := by nlinarith
        have h36 : sqrt (1 - c^2) ≥ 0 := by apply Real.sqrt_nonneg
        nlinarith [Real.sqrt_nonneg (1 - c^2)]
      linarith
    linarith
  linarith [h1, h2, h3]