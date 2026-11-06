import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_200943 (a : ℝ) :
  {x | a * x ^ 2 - abs (x + 1) + 2 * a < 0} = ∅ ↔
  a ≥ (Real.sqrt 3 + 1) / 4 := by 
  simp [Set.eq_empty_iff_forall_not_mem]
  constructor 
  · -- Forward: if solution set is empty, then a ≥ (sqrt(3) + 1)/4
    intro h
    by_contra ha 
    push_neg at ha
    have h1 := h (-1 + Real.sqrt 3)
    have h2 : abs ((-1 + Real.sqrt 3 : ℝ) + 1) = Real.sqrt 3 := by
      have h3 : (-1 + Real.sqrt 3 : ℝ) + 1 = Real.sqrt 3 := by
        linarith 
      rw [h3]
      rw [abs_of_nonneg (Real.sqrt_nonneg 3)]
    rw [h2] at h1
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), sq_nonneg (a - (Real.sqrt 3 + 1) / 4), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  · -- Backward: if a ≥ (sqrt(3) + 1)/4, then solution set is empty
    intro ha x
    by_cases h : x + 1 ≥ 0 
    · -- Case 1: x + 1 ≥ 0 → |x + 1| = x + 1.
      have h1 : abs (x + 1) = x + 1 := by 
        rw [abs_of_nonneg h]
      rw [h1]
      nlinarith [sq_nonneg (x - (-1 + Real.sqrt 3)), sq_nonneg (a - (Real.sqrt 3 + 1) / 4), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), sq_nonneg (x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Case 2: x + 1 < 0 → |x + 1| = -(x + 1).
      have h1 : abs (x + 1) = - (x + 1) := by 
        rw [abs_of_neg (lt_of_not_ge h)]
      rw [h1]
      nlinarith [sq_nonneg (x + 1 + Real.sqrt 3), sq_nonneg (a - (Real.sqrt 3 + 1) / 4), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), sq_nonneg (x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]