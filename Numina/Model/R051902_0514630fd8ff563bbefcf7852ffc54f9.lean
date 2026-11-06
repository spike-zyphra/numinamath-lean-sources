import Mathlib

theorem algebra_178319 (a b c d : ℝ) (h : a * b - c * d ≠ 0) :
    a^2 + b^2 > 0 ∨ c^2 + d^2 > 0 := by
  by_contra h1
  push_neg at h1
  have h2 : a^2 ≥ 0 := by apply sq_nonneg
  have h3 : b^2 ≥ 0 := by apply sq_nonneg
  have h4 : c^2 ≥ 0 := by apply sq_nonneg
  have h5 : d^2 ≥ 0 := by apply sq_nonneg
  have h6 : a = 0 := by
    have : a^2 = 0 := by linarith [h2, h3, h1.left]
    exact pow_eq_zero this
  have h7 : b = 0 := by
    have : b^2 = 0 := by linarith [h2, h3, h1.left]
    exact pow_eq_zero this
  have h8 : c = 0 := by
    have : c^2 = 0 := by linarith [h4, h5, h1.right]
    exact pow_eq_zero this
  have h9 : d = 0 := by
    have : d^2 = 0 := by linarith [h4, h5, h1.right]
    exact pow_eq_zero this
  have h10 : a * b - c * d = 0 := by
    rw [h6, h7, h8, h9]
    norm_num
  contradiction