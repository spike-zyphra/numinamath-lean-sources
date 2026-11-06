import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_156182 {x : ℝ} (hx : 0 < x) (h : x < 60 / 2) :
    (x * (60 - 2 * x) ^ 2) ≤ (10 * (60 - 2 * 10) ^ 2) := by
  have h1 : x < 30 := by
    linarith
  nlinarith [sq_nonneg (x - 10), sq_nonneg (x - 40),
    sq_nonneg (x * (x - 10)), sq_nonneg ((60 - 2 * x) - 40),
    mul_pos hx (show 0 < 30 - x by linarith), mul_nonneg (show 0 ≤ 30 - x by linarith) (show 0 ≤ x by linarith)]