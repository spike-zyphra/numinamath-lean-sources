import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_146106 {f : ℝ → ℝ}
  (hf : f = λ x => 2 * logb (sqrt 2) (sqrt 2 * x - 5) - 4) :
  ∃ x, f x = 0 ∧ x > 5 / sqrt 2 := by 
  use 7 * Real.sqrt 2 / 2
  constructor
  · -- Prove f x = 0
    rw [hf]
    have h1 : Real.sqrt 2 * (7 * Real.sqrt 2 / 2) - 5 = (2 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < (2: ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    simp_all [h1]
    have h2 : logb (Real.sqrt 2) (2 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h2]
    all_goals norm_num
  · -- Prove x > 5 / sqrt 2
    have h3 : (5 : ℝ) / Real.sqrt 2 < (7 * Real.sqrt 2 / 2 : ℝ) := by
      have h8 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (2 : ℝ))
      have h7 : (5 / Real.sqrt 2 : ℝ) = (5 * Real.sqrt 2 / 2 : ℝ) := by
        field_simp [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [h7]
      have h8 : (5 * Real.sqrt 2 / 2 : ℝ) < (7 * Real.sqrt 2 / 2 : ℝ) := by
        have h6 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
        have h9 : (5 * Real.sqrt 2 : ℝ) < (7 * Real.sqrt 2 : ℝ) := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
        linarith
      linarith
    linarith