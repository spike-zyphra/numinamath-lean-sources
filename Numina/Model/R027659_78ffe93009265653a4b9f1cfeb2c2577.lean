import Mathlib

theorem algebra_129594 {a : ℝ} (ha : a ≠ 0) :
    ∃ x : ℤ, x^2 - (a + 1 / a) * x + (a + Real.sqrt 35) * (1 / a - Real.sqrt 35) = 0 ↔
    a = 6 - Real.sqrt 35 := by
  use 6
  constructor
  · -- Assume the equation holds, prove a = 6 - Real.sqrt 35
    intro h
    norm_num at h 
    have eq1 : (6 : ℝ)^2 - (a + 1 / a) * (6 : ℝ) + (a + Real.sqrt 35) * (1 / a - Real.sqrt 35) = (0 : ℝ) := by
      norm_num at h ⊢
      nlinarith
    have eq2 : (a - (6 - Real.sqrt 35)) ^ 2 = 0 := by
      field_simp at eq1
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (35 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (35 : ℝ) by norm_num), sq_nonneg (a ^ 2 - 1), sq_nonneg (a ^ 2 - 12), sq_nonneg (a + (6 + Real.sqrt 35)), sq_nonneg (a - (6 - Real.sqrt 35)), sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (35 : ℝ) by norm_num)), Real.sq_sqrt (show (0 : ℝ) ≤ (35 : ℝ) by norm_num)]
    have ha2 : a - (6 - Real.sqrt 35) = 0 := by
      apply pow_eq_zero 
      exact eq2
    have ha3 : a = 6 - Real.sqrt 35 := by
      linarith
    assumption
  · -- Assume a = 6 - Real.sqrt 35, prove the equation holds
    intro h
    rw [h]
    have h1 : (6 - Real.sqrt 35 : ℝ) ≠ 0 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (35 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (35 : ℝ) by norm_num)]
    have h2 : 1 / (6 - Real.sqrt 35 : ℝ) = (6 + Real.sqrt 35 : ℝ) := by
      field_simp [h1]
      all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (35 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (35 : ℝ) by norm_num)]
    norm_num [h2]
    all_goals
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (35 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (35 : ℝ) by norm_num)]