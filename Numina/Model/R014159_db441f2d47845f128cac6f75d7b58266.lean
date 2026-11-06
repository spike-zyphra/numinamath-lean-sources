import Mathlib

theorem algebra_300530 {a b : ℝ} (ha : a * b = 1) :
    (1 / (1 + a ^ 2)) + (1 / (1 + b ^ 2)) = (a ^ 2 / (1 + a ^ 2)) + (b ^ 2 / (1 + b ^ 2)) := by
  have h2 : 1 + a ^ 2 ≠ 0 := by 
    nlinarith [sq_nonneg a]
  have h3 : 1 + b ^ 2 ≠ 0 := by 
    nlinarith [sq_nonneg b]
  have h5 : a * b = 1 := ha 
  field_simp [h2, h3]
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a), sq_nonneg (b), h5]