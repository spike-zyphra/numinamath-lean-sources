import Mathlib

open Complex

theorem algebra_94035 :
  (((-2):ℂ)^5).re ≤ ((-√3 + I)^5).re ∧
  ((-√2+√2*I)^5).re ≤ ((-√3 + I)^5).re ∧
  ((-1+√3*I)^5).re ≤ ((-√3 + I)^5).re ∧
  ((2*I)^5).re ≤ ((-√3 + I)^5).re := by
  constructor
  · -- Show that the real part of (-2)^5 ≤ (-√3 + I)^5.
    norm_num [pow_succ, pow_zero, Complex.add_re, Complex.mul_re, Complex.ofReal_re, 
      Complex.I_re, Complex.I_im, mul_add, pow_two, pow_succ]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      sq_nonneg (√3), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  constructor
  · -- Show that the real part of (-√2 + √2 * I)^5 ≤ (-√3 + I)^5.
    norm_num [pow_succ, pow_zero, Complex.add_re, Complex.mul_re, Complex.ofReal_re, 
      Complex.I_re, Complex.I_im, mul_add, pow_two, pow_succ]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      sq_nonneg (√3 - √2), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  constructor
  · -- Show that the real part of (-1 + √3 * I)^5 ≤ (-√3 + I)^5.
    norm_num [pow_succ, pow_zero, Complex.add_re, Complex.mul_re, Complex.ofReal_re, 
      Complex.I_re, Complex.I_im, mul_add, pow_two, pow_succ]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      sq_nonneg (√3), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  · -- Show that the real part of (2 * I)^5 ≤ (-√3 + I)^5.
    norm_num [pow_succ, pow_zero, Complex.add_re, Complex.mul_re, Complex.ofReal_re, 
      Complex.I_re, Complex.I_im, mul_add, pow_two, pow_succ]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      sq_nonneg (√3), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]