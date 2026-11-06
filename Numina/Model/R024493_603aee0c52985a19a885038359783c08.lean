import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_324239 (a : ℝ) :
  {x : ℝ | a * x^2 - abs (x + 1) + 2 * a < 0} = ∅ ↔
  a ≥ (Real.sqrt 3 + 1) / 4 := by

  have h1 : {x : ℝ | a * x^2 - abs (x + 1) + 2 * a < 0} = ∅ ↔ ∀ x : ℝ, a * x^2 - abs (x + 1) + 2 * a ≥ 0 := by
    have h2 : {x : ℝ | a * x^2 - abs (x + 1) + 2 * a < 0} = ∅ ↔ ∀ x : ℝ, a * x^2 - abs (x + 1) + 2 * a ≥ 0 := by
      simp [Set.eq_empty_iff_forall_not_mem, Set.mem_setOf_eq]
    exact h2

  rw [h1]

  constructor
  · -- Assume that for all x, a * x^2 - abs (x + 1) + 2 * a ≥ 0, show that a ≥ (sqrt(3) + 1)/4.
    intro h
    have h2 := h (-1 + Real.sqrt 3)
    have h3 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
    have h4 : Real.sqrt 3 > 0 := by
      positivity
    have h5 : abs ((-1 + Real.sqrt 3) + 1 : ℝ) = Real.sqrt 3 := by
      have h7 : (-1 + Real.sqrt 3) + 1 = Real.sqrt 3 := by
        nlinarith
      rw [h7]
      rw [abs_of_nonneg]
      positivity
    rw [h5] at h2
    have h8 : a * ((-1 + Real.sqrt 3) ^ 2) - Real.sqrt 3 + 2 * a ≥ 0 := by
      nlinarith
    have h9 : (-1 + Real.sqrt 3) ^ 2 = 4 - 2 * Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sqrt_nonneg 3]
    rw [h9] at h8
    have h10 : a ≥ (Real.sqrt 3 + 1) / 4 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), sq_nonneg (a - (Real.sqrt 3 + 1) / 4), Real.sqrt_nonneg 3, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    linarith
  · -- Assume a ≥ (sqrt(3) + 1)/4, show that {x | a * x^2 - abs (x + 1) + 2 * a < 0} = ∅.
    intro ha x
    have h1 : a ≥ (Real.sqrt 3 + 1) / 4 := by linarith
    have h2 : a * x^2 + 2 * a ≥ abs (x + 1) := by
      by_cases h3 : x + 1 ≥ 0
      · -- x + 1 ≥ 0
        rw [abs_of_nonneg h3]
        nlinarith [sq_nonneg (x - (-1 + Real.sqrt 3)), sq_nonneg (x - (-1 - Real.sqrt 3)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (a - (Real.sqrt 3 + 1) / 4), Real.sqrt_nonneg 3, mul_nonneg (show 0 ≤ a - (Real.sqrt 3 + 1) / 4 by nlinarith) (show 0 ≤ (1 : ℝ) by norm_num)]
      · -- x + 1 < 0
        rw [abs_of_neg (show x + 1 < 0 by linarith)]
        nlinarith [sq_nonneg (x - (-1 + Real.sqrt 3)), sq_nonneg (x - (-1 - Real.sqrt 3)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (a - (Real.sqrt 3 + 1) / 4), Real.sqrt_nonneg 3, mul_nonneg (show 0 ≤ a - (Real.sqrt 3 + 1) / 4 by nlinarith) (show 0 ≤ (1 : ℝ) by norm_num)]
    nlinarith