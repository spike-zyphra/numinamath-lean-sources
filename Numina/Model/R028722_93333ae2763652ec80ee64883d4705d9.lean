import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_110858 {f : ℝ → ℝ}
  (hf : f = λ x => 2 * (logb (1 / 2) x) ^ 2 - 2 * logb (1 / 2) x + 1) :
  MonotoneOn f (Ici (sqrt 2 / 2)) := by
  intro x hx y hy hxy
  have hx1 : x ≥ sqrt 2 / 2 := by
    simpa using hx
  have hy1 : y ≥ sqrt 2 / 2 := by
    simpa using hy
  have hxy1 : x ≤ y := hxy
  have h1 : f x = 2 * (logb (1 / 2) x) ^ 2 - 2 * logb (1 / 2) x + 1 := by
    rw [hf]
  have h2 : f y = 2 * (logb (1 / 2) y) ^ 2 - 2 * logb (1 / 2) y + 1 := by
    rw [hf]
  have h3 : logb (1 / 2) x = - logb 2 x := by
    have h4 : logb (1 / 2) x = logb 2 x / logb 2 (1 / 2) := by
      field_simp [logb]
    have h5 : logb 2 (1 / 2) = -1 := by
      rw [logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h4, h5]
    all_goals ring
  have h4 : logb (1 / 2) y = - logb 2 y := by
    have h4 : logb (1 / 2) y = logb 2 y / logb 2 (1 / 2) := by
      field_simp [logb]
    have h5 : logb 2 (1 / 2) = -1 := by
      rw [logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h4, h5]
    all_goals ring
  have h5 : logb 2 x ≤ logb 2 y := by
    apply Real.logb_le_logb_of_le
    all_goals
      have h100 : x ≥ sqrt 2 / 2 := by linarith
      have h101 : y ≥ sqrt 2 / 2 := by linarith
      have h102 : x > 0 := by
        have h130 : sqrt 2 > 0 := by
          positivity
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h103 : y > 0 := by
        have h130 : sqrt 2 > 0 := by
          positivity
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      all_goals
        nlinarith
  have h50 : logb 2 x ≥ -1 / 2 := by
    have h100 : x ≥ sqrt 2 / 2 := by linarith
    have h110 : logb 2 x ≥ logb 2 (sqrt 2 / 2) := by
      apply Real.logb_le_logb_of_le
      all_goals
        have h1000 : (2 : ℝ) > 1 := by norm_num
        have h1001 : sqrt 2 / 2 > 0 := by
          have h130 : sqrt 2 > 0 := by
            positivity
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        have h1002 : x > 0 := by
          have h130 : sqrt 2 > 0 := by
            positivity
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        all_goals
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h140 : logb 2 (sqrt 2 / 2) = -1 / 2 := by
      have h141 : logb 2 (sqrt 2 / 2) = logb 2 (sqrt 2) - logb 2 (2 : ℝ) := by
        rw [logb_div (by
          have h130 : sqrt 2 > 0 := by
            positivity
          linarith
        ) (by norm_num)]
      have h142 : logb 2 (sqrt 2) = 1 / 2 := by
        have h180 : sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
        rw [h180]
        have h181 : logb (2 : ℝ) ((2 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
          rw [logb_rpow]
          all_goals norm_num
        linarith
      have h143 : logb 2 (2 : ℝ) = 1 := by
        rw [logb_self_eq_one]
        all_goals norm_num
      linarith [h141, h142, h143]
    linarith [h110, h140]
  have h7 : (logb 2 x : ℝ) ^ 2 + (logb 2 x : ℝ) ≤ (logb 2 y : ℝ) ^ 2 + (logb 2 y : ℝ) := by
    have h70 : logb 2 y ≥ logb 2 x := h5
    have h71 : logb 2 x ≥ -1 / 2 := h50
    have h72 : logb 2 y ≥ -1 / 2 := by linarith [h5, h50]
    nlinarith [sq_nonneg (logb 2 x - logb 2 y), sq_nonneg (logb 2 x + 1 / 2), sq_nonneg (logb 2 y + 1 / 2)]
  have h8 : 2 * (logb (1 / 2) x : ℝ) ^ 2 - 2 * (logb (1 / 2) x : ℝ) + 1 ≤ 2 * (logb (1 / 2) y : ℝ) ^ 2 - 2 * (logb (1 / 2) y : ℝ) + 1 := by
    rw [h3, h4]
    nlinarith [h7, h5]
  rw [h1, h2]
  all_goals try linarith