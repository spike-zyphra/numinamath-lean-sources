import Mathlib

open Real Set
open scoped Real

theorem algebra_189189 {x : ℝ} (hx : x > 0) (h : cos (arctan x) = x) :
    x^2 = (-1 + sqrt 5) / 2 := by
  have h1 : cos (arctan x) = 1 / Real.sqrt (1 + x^2) := by
    rw [cos_arctan]
    <;> try tauto
  rw [h1] at h
  have h5 : x ^ 2 = (-1 + Real.sqrt 5) / 2 := by
    have h6 : Real.sqrt (1 + x^2) > 0 := by
      apply Real.sqrt_pos.mpr
      nlinarith [sq_nonneg x]
    have h4 : Real.sqrt (1 + x^2) = 1 / x := by
      field_simp [(show x ≠ 0 by linarith)] at h ⊢
      <;> nlinarith [Real.sqrt_pos.mpr (show 0 < 1 + x^2 by nlinarith), Real.sq_sqrt (show 0 ≤ 1 + x^2 by nlinarith), sq_nonneg x]
    have h7 : Real.sqrt (1 + x^2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by nlinarith)
    have h8 : (1 / x) ^ 2 = 1 / x ^ 2 := by field_simp
    rw [h4] at h7
    field_simp [(show x ≠ 0 by linarith)] at h7
    have h9 : 0 < x ^ 2 := by nlinarith
    have h10 : x ^ 2 * (1 + x ^ 2) = 1 := by
      nlinarith
    have h11 : (x ^ 2) ^ 2 + x ^ 2 - 1 = 0 := by
      nlinarith
    have h12 : (x ^ 2 - (-1 + Real.sqrt 5) / 2) * (x ^ 2 - (-1 - Real.sqrt 5) / 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h12) with h13 h14
    · -- x^2 - (-1 + sqrt 5)/2 = 0, so x^2 = (-1 + sqrt 5)/2
      linarith
    · -- x^2 - (-1 - sqrt 5)/2 = 0
      nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  exact h5