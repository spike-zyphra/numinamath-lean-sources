import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_160060 (z : ℂ) (hz : abs (z + 5 - 12 * I) = 3) :
    abs z ≤ 16 := by
  have h1 : abs z = Real.sqrt ((z.re) ^ 2 + (z.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  have h2 : abs (z + 5 - 12 * I) = Real.sqrt ((z.re + 5) ^ 2 + (z.im - 12) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h2] at hz
  have h3 : (z.re + 5) ^ 2 + (z.im - 12) ^ 2 = 9 := by
    calc
      (z.re + 5) ^ 2 + (z.im - 12) ^ 2 = (Real.sqrt ((z.re + 5) ^ 2 + (z.im - 12) ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 3 ^ 2 := by rw [hz]
      _ = 9 := by norm_num
  have h4 : (z.re) ^ 2 + (z.im) ^ 2 ≤ 256 := by
    nlinarith [sq_nonneg (z.re + 5), sq_nonneg (z.im - 12), sq_nonneg (z.re), sq_nonneg (z.im), sq_nonneg (z.re * 5 - z.im * 12), sq_nonneg (z.re * 12 + z.im * 5)]
  have h5 : abs z ≤ 16 := by
    rw [h1]
    have h6 : Real.sqrt ((z.re) ^ 2 + (z.im) ^ 2) ≤ (16 : ℝ) := by
      have h7 : (z.re) ^ 2 + (z.im) ^ 2 ≤ (256 : ℝ) := h4
      have h8 : Real.sqrt ((z.re) ^ 2 + (z.im) ^ 2) ≤ Real.sqrt (256 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h9 : Real.sqrt (256 : ℝ) = (16 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith
    linarith
  exact h5