import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_4602
  (z : ℂ) (hz : abs (6 * z - I / 2 + 3 * I * z) ≤ 1) :
  abs z ≤ 1 / 3 := by
  have h1 : abs (6 * z - I / 2 + 3 * I * z) = Real.sqrt ((6 * z.re - 3 * z.im) ^ 2 + (6 * z.im + 3 * z.re - 1 / 2) ^ 2) := by
    have h2 : (6 * z - I / 2 + 3 * I * z : ℂ) = (6 * z.re - 3 * z.im : ℝ) + I * (6 * z.im + 3 * z.re - 1 / 2 : ℝ) := by
      simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      <;> ring_nf <;> simp [Complex.I_re, Complex.I_im]
      <;> ring
    rw [h2]
    simp [Complex.abs, Complex.normSq]
    ring_nf
  rw [h1] at hz
  have h2 : (6 * z.re - 3 * z.im) ^ 2 + (6 * z.im + 3 * z.re - 1 / 2) ^ 2 ≤ 1 := by
    have h3 : Real.sqrt ((6 * z.re - 3 * z.im) ^ 2 + (6 * z.im + 3 * z.re - 1 / 2) ^ 2) ≤ (1 : ℝ) := hz
    have h4 : 0 ≤ (6 * z.re - 3 * z.im : ℝ) ^ 2 + (6 * z.im + 3 * z.re - 1 / 2) ^ 2 := by positivity
    have h5 : Real.sqrt ((6 * z.re - 3 * z.im) ^ 2 + (6 * z.im + 3 * z.re - 1 / 2) ^ 2) ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [h3, Real.sqrt_nonneg ((6 * z.re - 3 * z.im) ^ 2 + (6 * z.im + 3 * z.re - 1 / 2) ^ 2)]
    have h6 : Real.sqrt ((6 * z.re - 3 * z.im) ^ 2 + (6 * z.im + 3 * z.re - 1 / 2) ^ 2) ^ 2 = (6 * z.re - 3 * z.im) ^ 2 + (6 * z.im + 3 * z.re - 1 / 2) ^ 2 := Real.sq_sqrt (show 0 ≤ (6 * z.re - 3 * z.im) ^ 2 + (6 * z.im + 3 * z.re - 1 / 2) ^ 2 by positivity)
    nlinarith
  have h3 : z.re ^ 2 + z.im ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (z.re - (1 / 2) * z.im), sq_nonneg (z.re + 2 * z.im), sq_nonneg (z.im - 2 / 3 * z.re), sq_nonneg (z.im + 2 / 3 * z.re), sq_nonneg (z.re * 6 - z.im * 3), sq_nonneg (z.im * 6 + z.re * 3 - 1 / 2), sq_nonneg (z.re - z.im * (1 / 3)), sq_nonneg (z.re + 3 * z.im), sq_nonneg (z.re - 1 / 3), sq_nonneg (z.re * 3 + 1 / 2 - z.im * 6), sq_nonneg (z.im * 6 - 3 * z.re), sq_nonneg (z.re - (1 / 3 : ℝ) * z.im), sq_nonneg (z.re - 2 * z.im * 1 / 3)]
  have h4 : abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h4]
  have h5 : z.re ^ 2 + z.im ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := h3
  have h6 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≤ Real.sqrt ((1 / 3 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by linarith [h5])
  have h7 : Real.sqrt ((1 / 3 : ℝ) ^ 2) = (1 / 3 : ℝ) := by
    rw [Real.sqrt_sq (by norm_num)]
  rw [h7] at h6
  linarith [h6, h5]