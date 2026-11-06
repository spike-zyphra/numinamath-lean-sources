import Mathlib

open Real

theorem inequalities_5583 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    3 / 2 ≤ (1 - sqrt (a * b) - c) / (a + b) + (1 - sqrt (b * c) - a) / (b + c) +
    (1 - sqrt (c * a) - b) / (c + a) := by
  have h1 : 0 < a * b := by nlinarith
  have h2 : 0 < b * c := by nlinarith
  have h3 : 0 < c * a := by nlinarith

  have h4 : sqrt (a * b) ≤ (a + b) / 2 := by
    nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ (a * b : ℝ) by nlinarith), sq_nonneg (a - b), Real.sq_sqrt (show 0 ≤ (a * b : ℝ) by nlinarith)]
  have h5 : sqrt (b * c) ≤ (b + c) / 2 := by
    nlinarith [Real.sqrt_nonneg (b * c), Real.sq_sqrt (show 0 ≤ (b * c : ℝ) by nlinarith), sq_nonneg (b - c), Real.sq_sqrt (show 0 ≤ (b * c : ℝ) by nlinarith)]
  have h6 : sqrt (c * a) ≤ (c + a) / 2 := by
    nlinarith [Real.sqrt_nonneg (c * a), Real.sq_sqrt (show 0 ≤ (c * a : ℝ) by nlinarith), sq_nonneg (c - a), Real.sq_sqrt (show 0 ≤ (c * a : ℝ) by nlinarith)]

  have h7 : (1 - sqrt (a * b) - c) / (a + b) ≥ 1 / 2 := by
    have h7 : a + b = 1 - c := by linarith 
    rw [h7]
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [show sqrt (a * b) ≤ (a + b) / 2 by linarith [h4], Real.sqrt_nonneg (a * b), h4, h, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), Real.sq_sqrt (show 0 ≤ a * b by nlinarith)]
  have h8 : (1 - sqrt (b * c) - a) / (b + c) ≥ 1 / 2 := by
    have h8 : b + c = 1 - a := by linarith 
    rw [h8]
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [show sqrt (b * c) ≤ (b + c) / 2 by linarith [h5], Real.sqrt_nonneg (b * c), h5, h, sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c), Real.sq_sqrt (show 0 ≤ b * c by nlinarith)]
  have h9 : (1 - sqrt (c * a) - b) / (c + a) ≥ 1 / 2 := by
    have h9 : c + a = 1 - b := by linarith 
    rw [h9]
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [show sqrt (c * a) ≤ (c + a) / 2 by linarith [h6], Real.sqrt_nonneg (c * a), h6, h, sq_nonneg (c - a), sq_nonneg (b - c), sq_nonneg (b - a), Real.sq_sqrt (show 0 ≤ c * a by nlinarith)]
  linarith [h7, h8, h9]