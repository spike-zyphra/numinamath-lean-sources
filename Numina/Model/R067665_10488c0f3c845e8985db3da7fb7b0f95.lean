import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_114001 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (h : a + 2 * b = 6) :
  logb 10 a + 2 * logb 10 b ≤ 3 * logb 10 2 := by
  have h1 : a = 6 - 2 * b := by linarith
  have h2 : logb 10 a + 2 * logb 10 b = logb 10 (a * b ^ 2) := by
    have h3 : logb 10 a + 2 * logb 10 b = logb 10 a + logb 10 (b^2) := by
      have h4 : logb 10 (b^2) = 2 * logb 10 b := by
        simp [logb_pow]
        all_goals norm_num
        <;> linarith
      linarith [h4]
    have h5 : logb 10 a + logb 10 (b^2) = logb 10 (a * (b^2)) := by
      have h6 : logb 10 a + logb 10 (b^2) = logb 10 (a * (b^2)) := by
        rw [logb_mul (by positivity) (by positivity)]
      rw [h6]
      <;> ring_nf
      <;> norm_num
      all_goals positivity
    rw [h3, h5]
    <;> ring_nf
    <;> norm_num
    all_goals positivity
  have h3 : a * b ^ 2 ≤ 8 := by 
    rw [h1]
    nlinarith [sq_nonneg (b - 2), sq_nonneg (b), sq_nonneg (6 - 2 * b)]
  have h4 : logb 10 (a * b ^ 2) ≤ logb 10 (8 : ℝ) := by 
    apply Real.logb_le_logb_of_le 
    all_goals 
      nlinarith [h3, mul_pos (show 0 < a by assumption) (show 0 < b ^ 2 by positivity)]
  have h5 : logb 10 (8 : ℝ) = 3 * logb 10 2 := by 
    calc 
      logb 10 (8 : ℝ) = logb 10 ((2: ℝ) ^ 3) := by 
        have h21 : ((2 : ℝ) ^ 3 : ℝ) = (8 : ℝ) := by norm_num
        rw [h21]
      _ = 3 * logb 10 (2 : ℝ) := by 
        simp [logb_pow]
        all_goals norm_num 
        <;> ring_nf 
        all_goals positivity
  linarith [h2, h4, h5]
  all_goals positivity