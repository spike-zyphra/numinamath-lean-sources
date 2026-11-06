import Mathlib

open Real

theorem algebra_253187 {x : ℝ} (hx : 0 < x) (hx1 : 4 * x - 15 > 0) :
    logb 10 (2 * x) = 2 * logb 10 (4 * x - 15) ↔ x = 9 / 2 := by
  constructor
  · -- Assume logb 10 (2 * x) = 2 * logb 10 (4 * x - 15), prove x = 9 / 2
    intro h_eq
    have h1 : 2 * x > 0 := by linarith
    have h2 : (4 * x - 15) > 0 := by linarith
    have h3 : logb 10 (2 * x) = 2 * logb 10 (4 * x - 15) := h_eq
    have h4 : 2 * logb 10 (4 * x - 15) = logb 10 ((4 * x - 15) ^ 2) := by
      simp [logb_pow]
    have h5 : logb 10 (2 * x) = logb 10 ((4 * x - 15) ^ 2) := by
      linarith [h3, h4]
    have h6 : 2 * x = (4 * x - 15) ^ 2 := by
      have h7 : 2 * x > 0 := by nlinarith
      have h8 : (4 * x - 15) ^ 2 > 0 := by positivity
      have h9 : logb 10 (2 * x) = logb 10 ((4 * x - 15) ^ 2) := h5
      have h10 : 2 * x = (4 * x - 15) ^ 2 := by
        apply logb_injOn_pos (by norm_num) h7 h8 h9
      exact h10
    have h7 : 16 * x^2 - 122 * x + 225 = 0 := by
      nlinarith [h6]
    have h8 : (x - 9 / 2) * (16 * x - 25) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case where x = 9/2
      linarith
    · -- Case where 16x - 25 = 0, x = 25/16, which contradicts hx1
      have h11 : x = 25 / 16 := by linarith
      rw [h11] at hx1
      nlinarith
  · -- Assume x = 9/2, prove logb 10 (2 * x) = 2 * logb 10 (4 * x - 15)
    intro h_eq
    rw [h_eq]
    have h1 : 2 * (9 / 2 : ℝ) = 9 := by norm_num
    have h2 : (4 * (9 / 2 : ℝ) - 15) = 3 := by norm_num
    rw [h1, h2]
    have h3 : logb 10 (9 : ℝ) = 2 * logb 10 (3 : ℝ) := by
      rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num]
      simp [logb_pow]
    linarith [h3]