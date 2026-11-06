import Mathlib

theorem algebra_20481 (x : ℝ) (h : (4 * x ^ 2) ^ ((1 : ℝ) / 3) = 4) :
    x = -4 ∨ x = 4 := by
  have h1 : (4 * x ^ 2) = 4 ^ 3 := by
    have h2 : ((4 * x ^ 2) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = (4 : ℝ) ^ (3 : ℝ) := by
      rw [h]
      all_goals norm_num
    have h3 : ((4 * x ^ 2) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = (4 * x ^ 2) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals positivity
    have h4 : (4 : ℝ) ^ (3 : ℝ) = 64 := by
      norm_num
    have h5 : (4 * x ^ 2) = 64 := by
      linarith [h2, h3, h4]
    nlinarith
  have h5 : x^2 = 16 := by
    nlinarith
  have h6 : x = 4 ∨ x = -4 := by
    have h7 : x^2 - 16 = 0 := by
      linarith
    have h8 : (x - 4) * (x + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · left
      linarith
    · right
      linarith
  cases h6 with
  | inl h7 =>
    right
    exact h7
  | inr h7 =>
    left
    linarith