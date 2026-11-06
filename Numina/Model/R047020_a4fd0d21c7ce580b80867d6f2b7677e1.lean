import Mathlib

open Real


theorem Algebra_608307 {x y : ℝ} (h : (x + y) ^ 2 = (x + 1) * (y - 1)) : x = - 1 ∧ y = 1 := by
  have eq1 : x ^ 2 + x * y + y ^ 2 + x - y + 1 = 0 := by
    nlinarith
  have h2 : (x + 1) ^ 2 + (y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1), sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x + y), sq_nonneg (x + 1 - (y - 1)), sq_nonneg (x - (y - 2))]
  have h3 : x + 1 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1)]
  have h4 : y - 1 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1)]
  constructor
  · -- Prove x = -1
    linarith
  · -- Prove y = 1
    linarith