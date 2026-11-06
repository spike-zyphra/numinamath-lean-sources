import Mathlib

open Real

theorem inequalities_66559 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a + b + c + d = 4) :
    6 ≤ Real.sqrt (a + b + c) + Real.sqrt (b + c + d) + Real.sqrt (c + d + a) +
        Real.sqrt (d + a + b) := by
  have h1 : Real.sqrt (a + b + c) ≥ (a + b + c)/2 := by
    have h2 : (a + b + c) ≤ 4 := by
      nlinarith
    have h3 : 0 ≤ (a + b + c : ℝ) := by nlinarith
    have h4 : Real.sqrt (a + b + c) ≥ (a + b + c)/2 := by
      nlinarith [Real.sqrt_nonneg (a + b + c), Real.sq_sqrt (show 0 ≤ (a + b + c : ℝ) by nlinarith), sq_nonneg ((Real.sqrt (a + b + c)) - (a + b + c)/2)]
    linarith

  have h2 : Real.sqrt (b + c + d) ≥ (b + c + d)/2 := by
    have h3 : (b + c + d) ≤ 4 := by
      nlinarith
    have h4 : 0 ≤ (b + c + d : ℝ) := by nlinarith
    have h5 : Real.sqrt (b + c + d) ≥ (b + c + d)/2 := by
      nlinarith [Real.sqrt_nonneg (b + c + d), Real.sq_sqrt (show 0 ≤ (b + c + d : ℝ) by nlinarith), sq_nonneg ((Real.sqrt (b + c + d)) - (b + c + d)/2)]
    linarith

  have h3 : Real.sqrt (c + d + a) ≥ (c + d + a)/2 := by
    have h4 : (c + d + a) ≤ 4 := by
      nlinarith
    have h5 : 0 ≤ (c + d + a : ℝ) := by nlinarith
    have h6 : Real.sqrt (c + d + a) ≥ (c + d + a)/2 := by
      nlinarith [Real.sqrt_nonneg (c + d + a), Real.sq_sqrt (show 0 ≤ (c + d + a : ℝ) by nlinarith), sq_nonneg ((Real.sqrt (c + d + a)) - (c + d + a)/2)]
    linarith

  have h4 : Real.sqrt (d + a + b) ≥ (d + a + b)/2 := by
    have h5 : (d + a + b) ≤ 4 := by
      nlinarith
    have h6 : 0 ≤ (d + a + b : ℝ) := by nlinarith
    have h7 : Real.sqrt (d + a + b) ≥ (d + a + b)/2 := by
      nlinarith [Real.sqrt_nonneg (d + a + b), Real.sq_sqrt (show 0 ≤ (d + a + b : ℝ) by nlinarith), sq_nonneg ((Real.sqrt (d + a + b)) - (d + a + b)/2)]
    linarith

  have h5 : Real.sqrt (a + b + c) + Real.sqrt (b + c + d) + Real.sqrt (c + d + a) + Real.sqrt (d + a + b) ≥ (a + b + c)/2 + (b + c + d)/2 + (c + d + a)/2 + (d + a + b)/2 := by
    linarith [h1, h2, h3, h4]

  have h6 : (a + b + c)/2 + (b + c + d)/2 + (c + d + a)/2 + (d + a + b)/2 = 6 := by
    nlinarith

  linarith [h5, h6]