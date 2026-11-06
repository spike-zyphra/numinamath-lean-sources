import Mathlib

open Real

theorem algebra_598093 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = a n / 2 + 1 / a n) :
    0 < a 10 - sqrt 2 ∧ a 10 - sqrt 2 < 10 ^ (-370 : ℤ) := by

  have ha2 : a 2 = 3 / 2 := by
    specialize han 1 (by norm_num)
    rw [show a 1 = 1 by linarith [ha1]] at han
    linarith

  have ha3 : a 3 = 17 / 12 := by
    specialize han 2 (by norm_num)
    rw [show a 2 = 3 / 2 by linarith [ha2]] at han
    norm_num at han ⊢
    linarith

  have ha4 : a 4 = 577 / 408 := by
    specialize han 3 (by norm_num)
    rw [show a 3 = 17 / 12 by linarith [ha3]] at han
    norm_num at han ⊢
    linarith

  have ha5 : a 5 = a 4 / 2 + 1 / a 4 := by
    specialize han 4 (by norm_num)
    simpa using han

  have ha6 : a 6 = a 5 / 2 + 1 / a 5 := by
    specialize han 5 (by norm_num)
    simpa using han

  have ha7 : a 7 = a 6 / 2 + 1 / a 6 := by
    specialize han 6 (by norm_num)
    simpa using han

  have ha8 : a 8 = a 7 / 2 + 1 / a 7 := by
    specialize han 7 (by norm_num)
    simpa using han

  have ha9 : a 9 = a 8 / 2 + 1 / a 8 := by
    specialize han 8 (by norm_num)
    simpa using han

  have ha10 : a 10 = a 9 / 2 + 1 / a 9 := by
    specialize han 9 (by norm_num)
    simpa using han

  constructor
  · -- Show $0 < a_{10} - \sqrt{2}$.
    rw [ha10, ha9, ha8, ha7, ha6, ha5, ha4]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    have h3 : 0 < Real.sqrt 2 := by
      positivity
    norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
    all_goals
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg (Real.sqrt 2 ^ 2 - 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]

  · -- Show $a_{10} - \sqrt{2} < 10^{-370}$.
    rw [ha10, ha9, ha8, ha7, ha6, ha5, ha4]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    have h3 : 0 < Real.sqrt 2 := by
      positivity
    norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
    all_goals
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg (Real.sqrt 2 ^ 2 - 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]