import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_244425 (x y z w : ℝ) (h : x + y + z + w = 1) :
    x * w + 2 * y * w + 3 * x * y + 3 * z * w + 4 * x * z + 5 * y * z ≤ 3 / 2 := by 
  have h1 : w = 1 - x - y - z := by linarith
  rw [h1] 
  nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2),
          sq_nonneg ((1 - x - y - z) + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2)]