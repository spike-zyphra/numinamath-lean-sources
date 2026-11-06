import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_600856 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
  (hsum : x + y + z = 1) :
  2 * x ^ 2 + y + 3 * z ^ 2 ∈ Icc (19 / 24) 3 := by
  have h1 : y = 1 - x - z := by linarith
  rw [h1]
  constructor
  · -- Show that $2 * x ^ 2 + y + 3 * z ^ 2 \geq 19 / 24$
    nlinarith [sq_nonneg (x - 1 / 4), sq_nonneg (z - 1 / 6), 
      hsum, 
      mul_nonneg hx (show 0 ≤ 1 - x - z + z by linarith), 
      mul_nonneg hz (show 0 ≤ x + (1 - x - z) by linarith)]
  · -- Show that $2 * x ^ 2 + y + 3 * z ^ 2 \leq 3$
    nlinarith [sq_nonneg (x - 1), sq_nonneg (z - 1), 
      hsum, 
      mul_nonneg hx (show 0 ≤ 1 - x - z + z by linarith), 
      mul_nonneg hz (show 0 ≤ x + (1 - x - z) by linarith)]