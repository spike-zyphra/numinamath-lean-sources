import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_197403 :
  {a : ℝ | ∀ x, x^4 + (a - 2) * x^2 + a ≥ 0} = Ici (4 - 2 * sqrt 3) := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · -- Assume that ∀ x, x^4 + (a - 2) * x^2 + a ≥ 0, prove that a ≥ 4 - 2 * sqrt 3.
    intro h
    have h1 := h (Real.sqrt (sqrt 3 - 1))
    have h2 : (Real.sqrt (sqrt 3 - 1)) ^ 2 = sqrt 3 - 1 := by
      rw [Real.sq_sqrt]
      have h1' : sqrt 3 ≥ 1 := by
        have h3 : (1 : ℝ) < (3 : ℝ) := by norm_num
        have h4 : 1 < sqrt 3 := by
          rw [Real.lt_sqrt]
          all_goals norm_num
        linarith
      have h2' : sqrt 3 - 1 ≥ 0 := by
        linarith [h1']
      linarith
    have h3 : (Real.sqrt (sqrt 3 - 1)) ^ 4 = (4 - 2 * Real.sqrt 3) := by
      calc
        (Real.sqrt (sqrt 3 - 1)) ^ 4 = ((Real.sqrt (sqrt 3 - 1)) ^ 2) ^ 2 := by ring
        _ = (sqrt 3 - 1) ^ 2 := by
          rw [h2]
        _ = 4 - 2 * Real.sqrt 3 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h4 := h1
    rw [h3] at h4
    rw [show (Real.sqrt (sqrt 3 - 1)) ^ 2 = sqrt 3 - 1 by linarith [h2]] at h4
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), sq_nonneg (sqrt 3 - 2), sq_nonneg (sqrt 3 -1), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  · -- Assume a ≥ 4 - 2 * sqrt 3, prove that ∀ x, x^4 + (a - 2) * x^2 + a ≥ 0.
    intro ha x
    have h1 : a ≥ 4 - 2 * Real.sqrt 3 := by
      linarith
    nlinarith [sq_nonneg (x ^ 2 - (sqrt 3 - 1)), sq_nonneg (x ^ 2 + (sqrt 3 - 1)), sq_nonneg (x), sq_nonneg (x ^ 2 -1), sq_nonneg (x ^ 2 - (2 - a) / 2), sq_nonneg (x), Real.sqrt_nonneg 3, Real.sqrt_nonneg 3, sq_nonneg (a - 4), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x ^ 2 - 2)]