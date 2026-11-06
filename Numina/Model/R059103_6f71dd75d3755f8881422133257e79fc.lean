import Mathlib

open Real
open scoped BigOperators

theorem inequalities_1615 {a b : ℚ} (h : |a + b| < |a - b|) : a * b < 0 := by
  have h1 : (a + b) ^ 2 < (a - b) ^ 2 := by
    have h4 : |a + b| ^ 2 < |a - b| ^ 2 := by
      have h5 : |a + b| < |a - b| := h
      have h6 : |a + b| ≥ 0 := by positivity
      have h7 : |a - b| ≥ 0 := by positivity
      nlinarith [h5, h6, h7, sq_nonneg (|a + b| - |a - b|), sq_nonneg (|a + b| + |a - b|)]
    have h2 : (a + b) ^ 2 = (|a + b|) ^ 2 := by
      rw [sq_abs]
    have h3 : (a - b) ^ 2 = (|a - b|) ^ 2 := by
      rw [sq_abs]
    nlinarith [h2, h3, h4, sq_nonneg (a), sq_nonneg (b)]
  have h2 : a * b < 0 := by 
    nlinarith 
  exact h2