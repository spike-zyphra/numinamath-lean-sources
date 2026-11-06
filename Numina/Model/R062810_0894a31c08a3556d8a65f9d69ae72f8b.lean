import Mathlib

open Real

theorem inequalities_368 : (Real.sqrt 2 - 1) > (Real.sqrt 5 - 2) := by
  have h1 : Real.sqrt 2 + 1 > Real.sqrt 5 := by
    have h2 : (Real.sqrt 2 + 1) ^ 2 > (Real.sqrt 5) ^ 2 := by
      have h3 : (Real.sqrt 2 + 1) ^ 2 = 3 + 2 * (Real.sqrt 2) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h4 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
        rw [Real.sq_sqrt]
        norm_num
      rw [h3, h4]
      have h5 : Real.sqrt 2 > 1 := by
        have h6 : Real.sqrt 1 < Real.sqrt 2 := by
          apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        have h7 : Real.sqrt 1 = 1 := by
          rw [Real.sqrt_eq_cases]
          norm_num
        linarith [h6, h7]
      nlinarith [h5]
    have h5 : Real.sqrt 2 + 1 > 0 := by
      positivity
    have h6 : Real.sqrt 5 > 0 := by
      apply Real.sqrt_pos.mpr (by norm_num)
    nlinarith [h2, h5, h6]
    all_goals nlinarith
  linarith