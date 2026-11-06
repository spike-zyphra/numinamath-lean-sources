import Mathlib

theorem algebra_136482 (x y a : ℝ) (ha : 0 < a) (h1 : 3^x = a) (h2 : a^y = 81) :
    x * y = 4 := by
  have h3 : (3 : ℝ) ^ (x * y) = 81 := by
    calc
      (3 : ℝ) ^ (x * y) = ((3 ^ x) ^ y) := by
        rw [← Real.rpow_mul]
        ring
        all_goals norm_num
      _ = (a ^ y) := by
        rw [h1]
      _ = (81 : ℝ) := by
        linarith
  have h4 : x * y = 4 := by
    have h5 : (3 : ℝ) ^ (x * y) = (3 : ℝ) ^ (4 : ℝ) := by
      rw [h3]
      norm_num
    have h6 : x * y = (4 : ℝ) := by
      apply_fun (Real.logb 3) at h5
      have h7 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (x * y)) = Real.logb (3 : ℝ) ((3 : ℝ) ^ (4 : ℝ)) := by
        linarith [h5]
      have h8 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (x * y)) = x * y := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h9 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (4 : ℝ)) = (4 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h8, h9] at h7
      linarith
    linarith
  exact h4