import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_281495 (z : ℂ) (hz : abs (z - I) ≤ 1) :
    -2 * Real.sqrt 3 / 9 ≤ (z.re * (abs (z - I)^2 - 1)) ∧
    (z.re * (abs (z - I)^2 - 1)) ≤ 2 * Real.sqrt 3 / 9 := by

  have h1 : abs (z - I) = Real.sqrt (z.re^2 + (z.im - 1) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring
  have h2 : z.re^2 + (z.im - 1) ^ 2 ≤ 1 := by
    have h3 : abs (z - I) ≤ 1 := hz
    have h4 : abs (z - I) = Real.sqrt (z.re^2 + (z.im - 1) ^ 2) := h1
    rw [h4] at h3
    have h5 : Real.sqrt (z.re^2 + (z.im - 1) ^ 2) ≤ (1 : ℝ) := h3
    have h6 : Real.sqrt (z.re^2 + (z.im - 1) ^ 2) ≥ 0 := by positivity
    have h7 : z.re^2 + (z.im - 1) ^ 2 ≤ (1 : ℝ) := by
      by_contra h
      push_neg at h
      have h8 : Real.sqrt (z.re^2 + (z.im - 1) ^ 2) > (1 : ℝ) := by
        have h9 : z.re^2 + (z.im - 1) ^ 2 > (1 : ℝ) := by linarith
        have h10 : Real.sqrt (z.re^2 + (z.im - 1) ^ 2) > Real.sqrt (1 : ℝ) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
        have h11 : Real.sqrt ((1 : ℝ) : ℝ) = (1 : ℝ) := Real.sqrt_one
        linarith [h10, h11]
      linarith
    linarith
  have h3 : abs (z - I) ^ 2 = z.re^2 + (z.im - 1) ^ 2 := by
    calc 
      abs (z - I) ^ 2 = (Real.sqrt (z.re^2 + (z.im - 1) ^ 2)) ^ 2 := by rw [h1]
      _ = z.re^2 + (z.im - 1) ^ 2 := by rw [Real.sq_sqrt]; positivity
  have h4 : z.re * (abs (z - I) ^ 2 - 1) = z.re * (z.re^2 + (z.im - 1) ^ 2 - 1) := by 
    rw [h3]
  have h5 : -2 * Real.sqrt 3 / 9 ≤ (z.re * (abs (z - I) ^ 2 - 1)) := by 
    rw [h4]
    nlinarith [sq_nonneg (z.re ^ 2 + (z.im - 1) ^ 2 - 1 / 3), sq_nonneg (z.re + Real.sqrt 3 / 3), sq_nonneg (z.re - Real.sqrt 3 / 3), sq_nonneg ((z.im - 1) ^ 2 - 2 / 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h6 : (z.re * (abs (z - I) ^ 2 - 1)) ≤ 2 * Real.sqrt 3 / 9 := by 
    rw [h4]
    nlinarith [sq_nonneg (z.re ^ 2 + (z.im - 1) ^ 2 - 1 / 3), sq_nonneg (z.re + Real.sqrt 3 / 3), sq_nonneg (z.re - Real.sqrt 3 / 3), sq_nonneg ((z.im - 1) ^ 2 - 2 / 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  constructor
  · exact h5
  · exact h6