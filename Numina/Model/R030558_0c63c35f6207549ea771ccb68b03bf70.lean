import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_93195 {x : ℝ} (hx : x > 0) :
    x ^ logb 10 x = x ^ 3 / 100 ↔ x = 10 ∨ x = 100 := by
  constructor
  · -- Assume x ^ logb 10 x = x ^ 3 / 100, prove x = 10 ∨ x = 100
    intro h_eq
    have h1 : logb 10 (x ^ logb 10 x) = logb 10 (x ^ 3 / 100) := by
      rw [h_eq]
    have h2 : logb 10 (x ^ logb 10 x) = (logb 10 x) * (logb 10 x) := by
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith
    have h3 : logb 10 (x ^ 3 / 100) = 3 * (logb 10 x) - 2 := by
      have h4 : logb 10 (x ^ 3 / 100) = logb 10 (x ^ 3) - logb 10 (100 : ℝ) := by
        rw [logb_div (by positivity) (by norm_num)]
      have h5 : logb 10 (x ^ 3) = 3 * logb 10 x := by
        simp [logb_pow]
      have h6 : logb 10 (100 : ℝ) = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      rw [h4, h5, h6]
    rw [h2] at h1
    rw [h3] at h1
    have h4 : (logb 10 x - 1) * (logb 10 x - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- $\log_{10} x = 1$
      have h7 : logb 10 x = 1 := by linarith
      have h8 : x = 10 := by
        have h9 : x = (10 : ℝ) ^ (logb 10 x : ℝ) := by
          field_simp
        rw [h9, h7]
        norm_num
      left
      exact h8
    · -- $\log_{10} x = 2$
      have h7 : logb 10 x = 2 := by linarith
      have h8 : x = 100 := by
        have h9 : x = (10 : ℝ) ^ (logb 10 x : ℝ) := by
          field_simp
        rw [h9, h7]
        norm_num
      right
      exact h8
  · -- Assume x = 10 ∨ x = 100, prove x ^ logb 10 x = x ^ 3 / 100
    rintro (h_eq | h_eq)
    · -- Case x = 10
      rw [h_eq]
      have h1 : logb 10 (10 : ℝ) = 1 := by
        norm_num [logb_eq_iff_rpow_eq]
      rw [h1]
      norm_num
    · -- Case x = 100
      rw [h_eq]
      have h1 : logb 10 (100 : ℝ) = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      rw [h1]
      norm_num