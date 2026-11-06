import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_225235 (x : ℝ) (hx : 0 < x) (h : x < 50 / 2) :
    (x * (50 - 2 * x) * (80 - 2 * x)) ≤ (10 * (50 - 2 * 10) * (80 - 2 * 10)) := by 
  nlinarith [sq_nonneg (x - 10), sq_nonneg ((x - 10) * (x - 45)), sq_nonneg ((x - 10) * (x - 25 / 2)), sq_nonneg (x * (x - 10)), sq_nonneg ((x - 10) * (x - 40 / 2)), mul_pos hx (show 0 < 50 / 2 - x by linarith), mul_pos hx (show 0 < 80 / 2 - x by linarith), sq_nonneg (x * (x - 10)), sq_nonneg (x * (x - 40 / 2)), sq_nonneg ((x - 10) * (x - 25 / 2)), sq_nonneg ((x - 25 / 2) * (x - 45)), sq_nonneg ((x - 25 / 2) * (x - 25 / 2)), sq_nonneg ((x - 10) * (x - 5)), sq_nonneg ((x - 5) * (x - 40 / 2)), sq_nonneg ((x - 10) * (x - 25 / 2)), sq_nonneg ((x - 25 / 2) * (50 - 2 * x)), sq_nonneg ((x - 25 / 2) * (80 - 2 * x)), mul_pos (show 0 < 50 / 2 - x by linarith) (show 0 < 80 / 2 - x by linarith)]