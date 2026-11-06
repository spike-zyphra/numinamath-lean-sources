import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_298687 (c : ℝ) :
  (∀ x y : ℝ, x^2 + (y - 1)^2 = 1 → x + y + c ≥ 0) ↔
  c ≥ sqrt 2 - 1 := by 
  constructor
  · -- Assume: ∀ x y: ℝ, x^2 + (y - 1)^2 = 1 → x + y + c > 0. Prove: c ≥ sqrt 2 - 1
    intro h
    have h1 := h (-Real.sqrt 2 / 2) (1 - Real.sqrt 2 / 2) (by
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2, h1, sq_nonneg (Real.sqrt 2 - 0)]
    )
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  · -- Assume: c ≥ sqrt 2 - 1. Prove: ∀ x y: ℝ, x^2 + (y - 1)^2 = 1 → x + y + c ≥ 0
    intro h x y h_eq
    have h1 : x^2 + (y - 1)^2 = 1 := h_eq
    have h2 : x + y ≥ 1 - Real.sqrt 2 := by
      nlinarith [sq_nonneg (x + y - (1 - Real.sqrt 2)), sq_nonneg (x - (-Real.sqrt 2 / 2 : ℝ)), sq_nonneg ((y : ℝ) - (1 - Real.sqrt 2 / 2 : ℝ)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), sq_nonneg (y - 1 + x), sq_nonneg (y - 1 - x)]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h]