import Mathlib

open Real

theorem algebra_292831 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n > 0, a (n + 1) = (sqrt 3 * a n - 1) / (a n + sqrt 3)) :
    a 2004 = 2 + sqrt 3 := by

  have ha2 : a 2 = 2 - Real.sqrt 3 := by
    rw [han 1 (by norm_num), ha1]
    have h1 : Real.sqrt 3 > 0 := by positivity
    field_simp [(show 1 + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
  have ha3 : a 3 = Real.sqrt 3 - 2 := by
    rw [han 2 (by norm_num), ha2]
    have h1 : Real.sqrt 3 > 0 := by positivity
    field_simp [(show (2 - Real.sqrt 3 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have ha4 : a 4 = -1 := by
    rw [han 3 (by norm_num), ha3]
    have h1 : Real.sqrt 3 > 0 := by positivity
    field_simp [(show (Real.sqrt 3 - 2 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have ha5 : a 5 = -2 - Real.sqrt 3 := by
    rw [han 4 (by norm_num), ha4]
    have h1 : Real.sqrt 3 > 0 := by positivity
    field_simp [(show (-1 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have ha6 : a 6 = 2 + Real.sqrt 3 := by
    rw [han 5 (by norm_num), ha5]
    have h1 : Real.sqrt 3 > 0 := by positivity
    field_simp [(show (-2 - Real.sqrt 3 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have ha7 : a 7 = 1 := by
    rw [han 6 (by norm_num), ha6]
    have h1 : Real.sqrt 3 > 0 := by positivity
    field_simp [(show (2 + Real.sqrt 3 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  have h1 : ∀ k, a (6 * k + 6) = 2 + Real.sqrt 3 := by
    intro k
    induction k with
    | zero =>
      norm_num [ha6]
    | succ k ih =>
      have ha8 : a (6 * k + 7) = 1 := by
        rw [han (6 * k + 6) (by omega)]
        rw [ih]
        have h1 : Real.sqrt 3 > 0 := by positivity
        field_simp [(show (2 + Real.sqrt 3 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have ha9 : a (6 * k + 8) = 2 - Real.sqrt 3 := by
        rw [han (6 * k + 7) (by omega)]
        rw [ha8]
        have h1 : Real.sqrt 3 > 0 := by positivity
        field_simp [(show (1 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have ha10 : a (6 * k + 9) = Real.sqrt 3 - 2 := by
        rw [han (6 * k + 8) (by omega)]
        rw [ha9]
        have h1 : Real.sqrt 3 > 0 := by positivity
        field_simp [(show (2 - Real.sqrt 3 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have ha11 : a (6 * k + 10) = -1 := by
        rw [han (6 * k + 9) (by omega)]
        rw [ha10]
        have h1 : Real.sqrt 3 > 0 := by positivity
        field_simp [(show (Real.sqrt 3 - 2 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have ha12 : a (6 * k + 11) = -2 - Real.sqrt 3 := by
        rw [han (6 * k + 10) (by omega)]
        rw [ha11]
        have h1 : Real.sqrt 3 > 0 := by positivity
        field_simp [(show (-1 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have ha13 : a (6 * k + 12) = 2 + Real.sqrt 3 := by
        rw [han (6 * k + 11) (by omega)]
        rw [ha12]
        have h1 : Real.sqrt 3 > 0 := by positivity
        field_simp [(show (-2 - Real.sqrt 3 : ℝ) + Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      show a (6 * (k + 1) + 6) = 2 + Real.sqrt 3
      have hk : 6 * (k + 1) + 6 = 6 * k + 12 := by omega
      rw [hk] at *
      linarith

  have hk : 2004 = 6 * (333) + 6 := by omega
  rw [hk] at *
  specialize h1 333
  norm_num at h1 ⊢
  linarith