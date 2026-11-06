import Mathlib

theorem algebra_127721 (x y : ℝ) (h : x^2 + y^2 - 2 * x + 4 * y = 0) :
    x - 2 * y ≤ 10 ∧ 0 ≤ x - 2 * y := by
  have h1 : (x - 1) ^ 2 + (y + 2) ^ 2 = 5 := by
    nlinarith 
  constructor
  · -- Prove the maximum
    nlinarith [sq_nonneg ((x - 1) - 2 * (y + 2)), sq_nonneg ((x -1) * 2 + (y + 2)), sq_nonneg ((x - 1) - 2*(y + 2)), sq_nonneg ((x -1) + 2*(y + 2)), sq_nonneg (x - 1 - (y + 2)*1/2), sq_nonneg (2*(x-1) - (y+2)), mul_self_nonneg (x - 1), mul_self_nonneg (y + 2)]
  · -- Prove the minimum
    nlinarith [sq_nonneg ((x - 1) - 2 * (y + 2)), sq_nonneg ((x - 1) * 2 + (y + 2)), sq_nonneg ((x - 1) - 2*(y + 2)), sq_nonneg ((x - 1) + 2*(y + 2)), sq_nonneg (x - 1 - (y + 2)*1/2), sq_nonneg (2*(x-1) - (y+2)), mul_self_nonneg (x - 1), mul_self_nonneg (y + 2)]