import Mathlib

theorem algebra_196499 {x y : ℝ} (h : (x - 12)^2 + (y - 13)^2 + (x - y)^2 = 1 / 3) :
    x = 12 + 1 / 3 ∧ y = 12 + 2 / 3 := by 
  have h1 : (x - (12 + 1 / 3)) ^ 2 + (y - (12 + 2 / 3)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - (12 + 1 / 3)), sq_nonneg (y - (12 + 2 / 3)), sq_nonneg (x - y), sq_nonneg (x - 12), sq_nonneg (y - 13)]
  have hx1 : (x - (12 + 1 / 3)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - (12 + 1 / 3)), sq_nonneg (y - (12 + 2 / 3))]
  have hy1 : (y - (12 + 2 / 3)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - (12 + 1 / 3)), sq_nonneg (y - (12 + 2 / 3))]
  have hx2 : x - (12 + 1 / 3) = 0 := by 
    rwa [sq_eq_zero_iff] at hx1
  have hy2 : y - (12 + 2 / 3) = 0 := by 
    rwa [sq_eq_zero_iff] at hy1
  constructor
  · -- proof for x
    linarith
  · -- proof for y
    linarith