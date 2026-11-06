import Mathlib

theorem algebra_315314 {a b c : ℤ} (h : a^2 + b^2 + c^2 + 3 < a * b + 3 * b + 2 * c) :
    ∃ x y, x ≠ y ∧ x^2 - 2 * x - 3 = 0 ∧ y^2 - 2 * y - 3 = 0 ∧ x = a + b ∧ y = c - b := by
  have h1 : (a - b + 1)^2 + (b - 2)^2 + (c - 1)^2 < 2 := by
    nlinarith [sq_nonneg (a - b + 1), sq_nonneg (b - 2), sq_nonneg (c - 1)]
  have b_eq_2 : b - 2 = 0 := by
    nlinarith [sq_nonneg (a - b + 1), sq_nonneg (c - 1), h1]
  have b_eq_2' : b = 2 := by linarith
  have h7 : (a - 1)^2 + (c - 1)^2 < 2 := by 
    rw [show b = 2 by linarith [b_eq_2']] at h1
    nlinarith
  have h10 : a - 1 = 0 := by
    nlinarith [sq_nonneg (c - 1), h7]
  have h13 : c - 1 = 0 := by
    nlinarith [sq_nonneg (a - 1), h7]
  have h14 : a = 1 := by 
    linarith [h10]
  have h15 : c = 1 := by 
    linarith [h13]
  use 3, -1
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num [h14, b_eq_2', h15]