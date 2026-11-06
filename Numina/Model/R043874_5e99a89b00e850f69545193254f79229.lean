import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_190360 (a b : ℝ) (h : ∀ x ∈ Icc 0 1, |a * x + b| ≤ 1) :
    a * b ≤ 1 / 4 := by
  have h1 := h 0 (by norm_num)
  have h1' : -1 ≤ b := by linarith [abs_le.mp h1]
  have h1'' : b ≤ 1 := by linarith [abs_le.mp h1]
  have h2 := h 1 (by norm_num)
  have h2' : -1 ≤ a + b := by linarith [abs_le.mp h2]
  have h2'' : a + b ≤ 1 := by linarith [abs_le.mp h2]
  have h3 := h (1 / 2) (by norm_num)
  have h3' : -1 ≤ a * (1 / 2) + b := by linarith [abs_le.mp h3]
  have h3'' : a * (1 / 2) + b ≤ 1 := by linarith [abs_le.mp h3]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a + b + 1)]