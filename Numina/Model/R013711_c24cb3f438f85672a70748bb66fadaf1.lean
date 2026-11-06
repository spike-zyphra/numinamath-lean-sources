import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_123205 {f : ℝ → ℝ} (hf : f = λ x => cos x + logb 2 x)
  (a : ℝ) (ha : 0 < a) (h : f a = f (2 * a)) :
  f (2 * a) - f (4 * a) = -3 ∨ f (2 * a) - f (4 * a) = -1 := by
  have h1 : f a = cos a + logb 2 a := by 
    rw [hf]
  have h2 : f (2 * a) = cos (2 * a) + logb 2 (2 * a) := by 
    rw [hf]
  have h3 : f (4 * a) = cos (4 * a) + logb 2 (4 * a) := by 
    rw [hf]
  rw [h1, h2] at h
  have h4_pos : 0 < (2 * a : ℝ) := by nlinarith
  have h8_pos : 0 < (4 * a : ℝ) := by nlinarith
  have h5 : logb 2 (2 * a) = logb 2 2 + logb 2 a := by
    rw [logb_mul (by nlinarith) (by nlinarith)]
  have h6 : logb 2 (2 : ℝ) = 1 := by 
    norm_num [logb_eq_iff_rpow_eq]
  have h7 : logb 2 (2 * a) = 1 + logb 2 a := by
    rw [h5, h6]
  have h8 : logb 2 (4 * a) = logb 2 4 + logb 2 a := by
    rw [logb_mul (by nlinarith) (by nlinarith)]
  have h9 : logb 2 (4 : ℝ) = 2 := by
    rw [logb_eq_iff_rpow_eq] <;> norm_num
  have h10 : logb 2 (4 * a) = 2 + logb 2 a := by
    rw [h8, h9]
  simp only [h7] at h 
  have heq : cos a = cos (2 * a) + 1 := by 
    linarith 
  have heq2 : cos (2 * a) = 2 * cos a ^ 2 - 1 := by 
    rw [cos_two_mul]
  rw [heq2] at heq 
  have heq3 : cos a * (2 * cos a - 1) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp heq3) with h11 h12
  · -- cos a = 0
    have h111 : cos a = 0 := by linarith
    have cos2a : cos (2 * a) = -1 := by 
      have h2a : cos a = 0 := h111
      have : cos (2 * a) = 2 * cos a ^ 2 - 1 := by
        rw [cos_two_mul]
      rw [this, h2a]
      norm_num 
    have cos4a : cos (4 * a) = 1 := by 
      have : cos (4 * a) = 2 * cos (2 * a) ^ 2 - 1 := by 
        have : 4 * a = 2 * (2 * a) := by ring
        rw [this]
        rw [cos_two_mul]
      rw [this, cos2a]
      norm_num 
    have h12a : f (2 * a) - f (4 * a) = -3 := by
      rw [h2, h3]
      simp only [cos2a, cos4a, h7, h10]
      linarith 
    left 
    linarith 
  · -- 2 * cos a - 1 = 0
    have h121 : 2 * cos a - 1 = 0 := by linarith 
    have cos_a : cos a = 1 / 2 := by linarith 
    have cos2a : cos (2 * a) = -1 / 2 := by 
      have h : cos (2 * a) = 2 * cos a ^ 2 - 1 := by 
        rw [cos_two_mul]
      rw [h, cos_a]
      norm_num 
    have cos4a : cos (4 * a) = -1 / 2 := by 
      have h : cos (4 * a) = 2 * cos (2 * a) ^ 2 - 1 := by 
        have : 4 * a = 2 * (2 * a) := by ring 
        rw [this]
        rw [cos_two_mul]
      rw [h, cos2a]
      norm_num 
    have h12a : f (2 * a) - f (4 * a) = -1 := by 
      rw [h2, h3]
      simp only [cos2a, cos4a, h7, h10]
      linarith 
    right 
    linarith