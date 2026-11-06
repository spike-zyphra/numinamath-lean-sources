import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_275512 (z : ℂ) (hz : abs z = 1) :
    abs (z + 1 + I * (7 - z)) ≠ 5 * Real.sqrt 3 := by 
  by_contra h
  have h1 : abs (z + 1 + I * (7 - z)) = 5 * Real.sqrt 3 := by
    exact_mod_cast h
  have h2 : abs z = 1 := hz
  have h3 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h4 : abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      all_goals
        ring_nf
    rw [h4] at h2
    have h5 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := by
      linarith
    have h6 : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 1 ^ 2 := by rw [h5]
        _ = 1 := by norm_num
    linarith
  have h7 : abs (z + 1 + I * (7 - z)) = Real.sqrt ((z.re + 1 + z.im) ^ 2 + (z.im + 7 - z.re) ^ 2) := by
    simp [Complex.abs, Complex.normSq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
    all_goals
      ring_nf
  rw [h7] at h1
  have h8 : Real.sqrt ((z.re + 1 + z.im) ^ 2 + (z.im + 7 - z.re) ^ 2) = 5 * Real.sqrt 3 := by
    linarith
  have h9 : (z.re + 1 + z.im) ^ 2 + (z.im + 7 - z.re) ^ 2 = 75 := by
    calc
      (z.re + 1 + z.im) ^ 2 + (z.im + 7 - z.re) ^ 2 = (Real.sqrt ((z.re + 1 + z.im) ^ 2 + (z.im + 7 - z.re) ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = (5 * Real.sqrt 3) ^ 2 := by rw [h8]
      _ = 25 * (Real.sqrt 3) ^ 2 := by ring
      _ = 25 * 3 := by rw [Real.sq_sqrt]; positivity
      _ = 75 := by norm_num
  nlinarith [sq_nonneg (z.re - 4 / 5), sq_nonneg (z.im - 3 / 5), sq_nonneg (z.re - 3 / 5), sq_nonneg (z.im - 4 / 5), Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num : (0:ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (z.re - z.im), sq_nonneg (z.re + z.im - 4 / 5), sq_nonneg (z.re - 3 / 5), sq_nonneg (z.im - 4 / 5)]