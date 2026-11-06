import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_292594 {x : ℝ} (hx : 0 < x) (h : x ≤ 25) :
    (80 - 2 * x) * (50 - 2 * x) * (x) ≤ (80 - 2 * 10) * (50 - 2 * 10) * 10 := by
  suffices (80 - 2 * x) * (50 - 2 * x) * (x) - (80 - 2 * 10) * (50 - 2 * 10) * 10 ≤ 0 by
    linarith
  have h4 : (80 - 2 * x) * (50 - 2 * x) * (x) - (80 - 2 * 10) * (50 - 2 * 10) * 10 =
      4 * ((x - 10) ^ 2 * (x - 45)) := by
    ring
  rw [h4]
  have h3 : (x - 10) ^ 2 * (x - 45) ≤ 0 := by
    have h4 : x - 45 ≤ 0 := by
      linarith
    have h5 : (x - 10) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith
  linarith [sq_nonneg (x - 10), sq_nonneg (x - 45), h3]