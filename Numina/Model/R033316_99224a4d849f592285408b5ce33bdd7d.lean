import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_298298 (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
  (hsum : u + v + w = 2) :
  0 ≤ u^2 * v^2 + v^2 * w^2 + w^2 * u^2 ∧ u^2 * v^2 + v^2 * w^2 + w^2 * u^2 ≤ 1 := by
  have h1 : w = 2 - u - v := by linarith
  have h2 : 0 ≤ 2 - u - v := by nlinarith [hsum, hu, hv]
  constructor
  · -- Show that 0 ≤ u^2 * v^2 + v^2 * w^2 + w^2 * u^2
    positivity
  · -- Show that u^2 * v^2 + v^2 * w^2 + w^2 * u^2 ≤ 1
    rw [h1]
    nlinarith [sq_nonneg (u * v - 1), sq_nonneg (u * (2 - u - v) - 0), sq_nonneg (v * (2 - u - v) - 0),
              sq_nonneg (u - 1), sq_nonneg (v - 1), sq_nonneg ((2 - u - v) - 1),
              mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ v by linarith),
              mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ 2 - u - v by nlinarith),
              mul_nonneg (show 0 ≤ v by linarith) (show 0 ≤ 2 - u - v by nlinarith)]