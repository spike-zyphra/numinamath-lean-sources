import Mathlib

theorem inequalities_601605 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) + Real.sqrt (4 * d + 1) < 6 := by
  have h1 : 0 ≤ a := by linarith
  have h2 : 0 ≤ b := by linarith
  have h3 : 0 ≤ c := by linarith
  have h4 : 0 ≤ d := by linarith

  have h5 : Real.sqrt (4 * a + 1) < 1 + 2 * a := by
    have h5 : (4 * a + 1 : ℝ) ≥ 0 := by nlinarith
    have h6 : 0 ≤ (4 * a + 1 : ℝ) := by nlinarith
    have h7 : (1 + 2 * a : ℝ) ≥ 0 := by nlinarith
    have h8 : Real.sqrt (4 * a + 1) < 1 + 2 * a := by
      nlinarith [Real.sqrt_nonneg (4 * a + 1), Real.sq_sqrt (show 0 ≤ (4 * a + 1 : ℝ) by nlinarith), sq_pos_of_pos ha, mul_pos ha ha]
    linarith

  have h6 : Real.sqrt (4 * b + 1) < 1 + 2 * b := by
    have h5 : (4 * b + 1 : ℝ) ≥ 0 := by nlinarith
    have h6 : 0 ≤ (4 * b + 1 : ℝ) := by nlinarith
    have h7 : (1 + 2 * b : ℝ) ≥ 0 := by nlinarith
    have h8 : Real.sqrt (4 * b + 1) < 1 + 2 * b := by
      nlinarith [Real.sqrt_nonneg (4 * b + 1), Real.sq_sqrt (show 0 ≤ (4 * b + 1 : ℝ) by nlinarith), sq_pos_of_pos hb, mul_pos hb hb]
    linarith

  have h7 : Real.sqrt (4 * c + 1) < 1 + 2 * c := by
    have h5 : (4 * c + 1 : ℝ) ≥ 0 := by nlinarith
    have h6 : 0 ≤ (4 * c + 1 : ℝ) := by nlinarith
    have h7 : (1 + 2 * c : ℝ) ≥ 0 := by nlinarith
    have h8 : Real.sqrt (4 * c + 1) < 1 + 2 * c := by
      nlinarith [Real.sqrt_nonneg (4 * c + 1), Real.sq_sqrt (show 0 ≤ (4 * c + 1 : ℝ) by nlinarith), sq_pos_of_pos hc, mul_pos hc hc]
    linarith

  have h8 : Real.sqrt (4 * d + 1) < 1 + 2 * d := by
    have h5 : (4 * d + 1 : ℝ) ≥ 0 := by nlinarith
    have h6 : 0 ≤ (4 * d + 1 : ℝ) := by nlinarith
    have h7 : (1 + 2 * d : ℝ) ≥ 0 := by nlinarith
    have h8 : Real.sqrt (4 * d + 1) < 1 + 2 * d := by
      nlinarith [Real.sqrt_nonneg (4 * d + 1), Real.sq_sqrt (show 0 ≤ (4 * d + 1 : ℝ) by nlinarith), sq_pos_of_pos hd, mul_pos hd hd]
    linarith

  have h10 : (1 + 2 * a) + (1 + 2 * b) + (1 + 2 * c) + (1 + 2 * d) = 6 := by
    nlinarith [h]

  have h19 : Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) + Real.sqrt (4 * d + 1) < (1 + 2 * a) + (1 + 2 * b) + (1 + 2 * c) + (1 + 2 * d) := by
    linarith [h5, h6, h7, h8]

  linarith [h19, h10]