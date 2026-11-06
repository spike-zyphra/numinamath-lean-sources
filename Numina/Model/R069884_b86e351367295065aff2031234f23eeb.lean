import Mathlib

open Real

theorem inequalities_130158 : (3 < √2 + √3 ∧ √2 + √3 < √10) := by
  have h1 : 3 < Real.sqrt 2 + Real.sqrt 3 := by
    have h11 : Real.sqrt 2 > (14 / 10 : ℝ) := by
      have h14 : ( (14 / 10 : ℝ) )^2 < (2 : ℝ) := by
        norm_num
      have h15 : (14 / 10 : ℝ) < Real.sqrt 2 := by
        have h12 : (14 / 10 : ℝ) ^ 2 < (2 : ℝ) := by norm_num
        have h16 : (0 : ℝ) < (14 / 10 : ℝ) := by norm_num
        have h14 : Real.sqrt ((14 / 10 : ℝ) ^ 2) = (14 / 10 : ℝ) := by
          rw [Real.sqrt_sq (by nlinarith)]
        have h17 : Real.sqrt ((14 / 10 : ℝ) ^ 2) < Real.sqrt (2 : ℝ) := by
          apply Real.sqrt_lt_sqrt (by nlinarith) (by linarith)
        linarith [h14, h17]
      linarith
    have h19 : Real.sqrt 3 > (17 / 10 : ℝ) := by
      have h20 : Real.sqrt ((17 / 10 : ℝ) ^ 2) = (17 / 10 : ℝ) := by
        rw [Real.sqrt_sq]
        all_goals norm_num
      have h21 : Real.sqrt ((17 / 10 : ℝ) ^ 2) < Real.sqrt (3 : ℝ) := by
        apply Real.sqrt_lt_sqrt
        all_goals nlinarith
      linarith [h20, h21]
    linarith [h11, h19]
  have h2 : Real.sqrt 2 + Real.sqrt 3 < Real.sqrt 10 := by
    have h3 : (Real.sqrt 2 + Real.sqrt 3) ^ 2 < (Real.sqrt 10) ^ 2 := by
      have h41 : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = (Real.sqrt 2) ^ 2 + (Real.sqrt 3) ^ 2 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by ring
      have h42 : (Real.sqrt 10) ^ 2 = (10 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)
      have h43 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h44 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      have h45 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
        calc
          Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3) := by
            rw [Real.sqrt_mul (by norm_num)]
          _ = Real.sqrt 6 := by norm_num
      rw [h41, h43, h44, h45]
      rw [h42]
      have h46 : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.sqrt_nonneg 10, h46, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num)]
    have h3a : 0 < Real.sqrt 2 + Real.sqrt 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
    have h3b : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), h3, h3a, h3b]
  constructor
  · exact h1
  · exact h2