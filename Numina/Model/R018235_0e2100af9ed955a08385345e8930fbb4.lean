import Mathlib

open Real

theorem inequalities_224695 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    3 / sqrt (a ^ 2 + 1) + 4 / sqrt (b ^ 2 + 1) + 12 / sqrt (c ^ 2 + 1) < 39 / 2 := by

  have ha1 : sqrt (a ^ 2 + 1) > 0 := by positivity
  have hb1 : sqrt (b ^ 2 + 1) > 0 := by positivity
  have hc1 : sqrt (c ^ 2 + 1) > 0 := by positivity

  have h1 : 3 / sqrt (a ^ 2 + 1) < 3 := by
    have h7 : sqrt (a ^ 2 + 1) > 1 := by
      have h8 : a ^ 2 > 0 := by nlinarith
      have h9 : a ^ 2 + 1 > 1 := by nlinarith
      have h10 : sqrt (a ^ 2 + 1) > sqrt (1 : ℝ) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
      have h11 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith

  have h2 : 4 / sqrt (b ^ 2 + 1) < 4 := by
    have h7 : sqrt (b ^ 2 + 1) > 1 := by
      have h8 : b ^ 2 > 0 := by nlinarith
      have h9 : b ^ 2 + 1 > 1 := by nlinarith
      have h10 : sqrt (b ^ 2 + 1) > sqrt (1 : ℝ) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
      have h11 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith

  have h3 : 12 / sqrt (c ^ 2 + 1) < 12 := by
    have h7 : sqrt (c ^ 2 + 1) > 1 := by
      have h8 : c ^ 2 > 0 := by nlinarith
      have h9 : c ^ 2 + 1 > 1 := by nlinarith
      have h10 : sqrt (c ^ 2 + 1) > sqrt (1 : ℝ) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
      have h11 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith

  have h4 : 3 / sqrt (a ^ 2 + 1) + 4 / sqrt (b ^ 2 + 1) + 12 / sqrt (c ^ 2 + 1) < 3 + 4 + 12 := by
    linarith [h1, h2, h3]

  nlinarith