import Mathlib

theorem algebra_296989 {x : ℝ} (hx : x > 0) (θ : ℝ) (h : Real.logb 2 x = 3 + 2 * Real.cos θ) :
    abs (x - 2) + abs (x - 33) = 31 := by
  have h1 : x = (2 : ℝ) ^ (3 + 2 * Real.cos θ) := by
    have h2 : Real.logb 2 x = 3 + 2 * Real.cos θ := h
    have h3 : x = (2 : ℝ) ^ (Real.logb 2 x) := by
      rw [Real.rpow_logb]
      all_goals linarith [show 0 < 2 by norm_num, show 2 ≠ 1 by norm_num, hx]
    rw [h3, h2]
  
  have hcos1 : -1 ≤ Real.cos θ := by
    apply Real.neg_one_le_cos

  have hcos2 : Real.cos θ ≤ 1 := by
    apply Real.cos_le_one

  have h4 : 1 ≤ (3 + 2 * Real.cos θ) := by
    linarith [hcos1]

  have h5 : (3 + 2 * Real.cos θ) ≤ 5 := by
    linarith [hcos2]

  have hx1 : 2 ≤ x := by
    rw [h1]
    have h2 : (2 : ℝ) ^ (3 + 2 * Real.cos θ) ≥ (2 : ℝ) ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      all_goals nlinarith
      all_goals nlinarith
    have h3 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by
      norm_num [Real.rpow_natCast]
    have h4 : (2 : ℝ) ^ (3 + 2 * Real.cos θ) ≥ (2 : ℝ) := by linarith [h2, h3]
    linarith

  have hx2 : x ≤ (32 : ℝ) := by
    rw [h1]
    have h5 : (3 + 2 * Real.cos θ) ≤ 5 := by linarith [hcos2]
    have h6 : (2 : ℝ) ^ (3 + 2 * Real.cos θ) ≤ (2 : ℝ) ^ (5 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      all_goals nlinarith
    have h7 : (2 : ℝ) ^ (5 : ℝ) = (32 : ℝ) := by
      norm_num [Real.rpow_natCast]
    have h8 : (2 : ℝ) ^ (3 + 2 * Real.cos θ) ≤ (32 : ℝ) := by linarith [h6, h7]
    linarith
  
  have h6 : x - 2 ≥ 0 := by linarith [hx1]
  have h7 : x - 33 ≤ 0 := by linarith [hx2]
  
  rw [abs_of_nonneg h6, abs_of_nonpos h7]
  linarith