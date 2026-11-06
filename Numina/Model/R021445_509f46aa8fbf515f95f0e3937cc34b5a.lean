import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_37537 {A : ℝ} :
  (∀ x y, x * y = 1 → ((x + y)^2 + 4) * ((x + y)^2 - 2) ≥ A * (x - y)^2) ↔
  A ≤ 18 :=
by
  constructor
  · -- Assume that inequality holds for all x y such that xy = 1, prove A ≤ 18
    intro h
    have h1 := h (1 + Real.sqrt 2) (Real.sqrt 2 - 1) (by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    )
    have h2 : ((1 + Real.sqrt 2 + (Real.sqrt 2 - 1)) ^ 2 + 4) * ((1 + Real.sqrt 2 + (Real.sqrt 2 - 1)) ^ 2 - 2) = 72 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : ( (1 + Real.sqrt 2) - (Real.sqrt 2 - 1) ) ^ 2 = (4 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    nlinarith [h2, h3, h1]
  · -- Assume that A ≤ 18, prove the inequality holds
    intro h x y hxy
    have h1 : (x + y)^2 - (x - y) ^ 2 = 4 := by
      have h2 : x * y = 1 := hxy
      nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - 1)]
    have h2 : ((x + y) ^ 2 + 4) * ((x + y) ^ 2 - 2) ≥ 18 * (x - y) ^ 2 := by
      nlinarith [sq_nonneg ((x + y) ^ 2 - 8), sq_nonneg ((x - y) ^ 2 - 4), sq_nonneg ((x + y) ^ 2 - (x - y) ^ 2 - 4), sq_nonneg (x * y - 1)]
    have h3 : A * (x - y) ^ 2 ≤ 18 * (x - y) ^ 2 := by
      have h4 : A ≤ (18 : ℝ) := h
      have h5 : (A : ℝ) * (x - y) ^ 2 ≤ (18 : ℝ) * (x - y) ^ 2 := by
        apply mul_le_mul_of_nonneg_right h4
        nlinarith [sq_nonneg (x - y)]
      linarith
    linarith [h2, h3, sq_nonneg ((x + y) ^ 2 - 8), sq_nonneg ((x - y) ^ 2 - 4), sq_nonneg (x * y - 1)]