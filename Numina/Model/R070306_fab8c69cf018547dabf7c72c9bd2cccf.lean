import Mathlib

open Real Set

theorem inequalities_60067 (x : ℝ) (y : ℝ) (h : x ^ 2 + 2 * cos y = 1) :
    -1 ≤ x - cos y ∧ x - cos y ≤ 1 + sqrt 3 := by
  have h1 : cos y = (1 - x^2) / 2 := by
    linarith
  have h2 : -1 ≤ cos y ∧ cos y ≤ 1 := by
    apply cos_mem_Icc
  have h3 : -1 ≤ (1 - x^2) / 2 := by linarith [h1, h2.left]
  have h4 : (1 - x^2) / 2 ≤ 1 := by linarith [h1, h2.right]
  have h5 : x ^ 2 ≤ 3 := by nlinarith
  have h6 : -1 ≤ x - cos y := by
    rw [h1]
    nlinarith [sq_nonneg (x + 1)]
  have h7 : x - cos y ≤ 1 + sqrt 3 := by
    rw [h1]
    nlinarith [sq_nonneg (x - sqrt 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), sq_nonneg (x ^ 2 - 3)]
  constructor
  · linarith [h6]
  · linarith [h7]