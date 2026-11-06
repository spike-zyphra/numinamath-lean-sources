import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_249048 (x y : ℝ) (h : 5 * x + 12 * y = 60) :
    sqrt (x ^ 2 + y ^ 2) ≥ 60 / 13 := by
  have h1 : x ^ 2 + y ^ 2 ≥ (60 / 13) ^ 2 := by
    nlinarith [sq_nonneg (x - 300 / 169), sq_nonneg (y - 720 / 169),
      sq_nonneg (5 * x + 12 * y - 60)]
  have h2 : sqrt (x ^ 2 + y ^ 2) ≥ sqrt ((60 / 13) ^ 2) := Real.sqrt_le_sqrt (show (60 / 13) ^ 2 ≤ x ^ 2 + y ^ 2 by linarith [h1])
  have h3 : sqrt ((60 / 13) ^ 2) = 60 / 13 := by
    rw [Real.sqrt_sq (by norm_num)]
  linarith [h2, h3]