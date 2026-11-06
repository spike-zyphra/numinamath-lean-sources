import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_141934 (x : ℝ) (hx : 3 / 2 ≤ x ∧ x ≤ 5) :
    2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) < 2 * sqrt 19 := by
  have h1 : 3 / 2 ≤ x := hx.1
  have h2 : x ≤ 5 := hx.2
  have h3 : x + 1 ≥ 0 := by linarith
  have h4 : 2 * x - 3 ≥ 0 := by linarith
  have h5 : 15 - 3 * x ≥ 0 := by linarith
  have h6 : (2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x)) ^ 2 < (2 * sqrt 19) ^ 2 := by
    have h7 : (2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x)) ^ 2 =
        4 * (sqrt (x + 1)) ^ 2 + (sqrt (2 * x - 3)) ^ 2 + (sqrt (15 - 3 * x)) ^ 2 + 4 * (sqrt (x + 1) * sqrt (2 * x - 3)) + 4 * (sqrt (x + 1) * sqrt (15 - 3 * x)) + 2 * (sqrt (2 * x - 3) * sqrt (15 - 3 * x)) := by
      ring
    have h8 : (2 * sqrt 19) ^ 2 = 4 * 19 := by
      ring_nf
      <;> norm_num [Real.sq_sqrt]
    rw [h7, h8]
    have h9 : (sqrt (x + 1)) ^ 2 = x + 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h10 : (sqrt (2 * x - 3)) ^ 2 = 2 * x - 3 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h11 : (sqrt (15 - 3 * x)) ^ 2 = 15 - 3 * x := by
      rw [Real.sq_sqrt]
      nlinarith
    rw [h9, h10, h11]
    have h12 : sqrt (x + 1) * sqrt (2 * x - 3) ≥ 0 := by
      positivity
    have h13 : sqrt (x + 1) * sqrt (15 - 3 * x) ≥ 0 := by
      positivity
    have h14 : sqrt (2 * x - 3) * sqrt (15 - 3 * x) ≥ 0 := by
      positivity
    nlinarith [sq_nonneg (2 * Real.sqrt (x + 1) - Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)), sq_nonneg (Real.sqrt (x + 1) - 2 * Real.sqrt (2 * x - 3)), sq_nonneg (Real.sqrt (x + 1) - 2 * Real.sqrt (15 - 3 * x)), sq_nonneg (Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg (19 : ℝ) ) (Real.sqrt_nonneg (x + 1) ), mul_nonneg (Real.sqrt_nonneg (19 : ℝ) ) (Real.sqrt_nonneg (2 * x - 3) ), mul_nonneg (Real.sqrt_nonneg (19 : ℝ) ) (Real.sqrt_nonneg (15 - 3 * x) ), Real.sqrt_nonneg (19 : ℝ) ]
  nlinarith [Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), Real.sqrt_nonneg 19, Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x - 3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (15 - 3 * x : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num) ]