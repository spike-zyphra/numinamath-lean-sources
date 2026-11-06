import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_196745 (x : ℝ) (hx : 0 < x) (h : x ≤ 60 / 2) :
    (x * (60 - 2 * x) ^ 2) ≤ 16000 := by
  nlinarith [sq_nonneg (x - 10), sq_nonneg ((60 - 2 * x) - 40),
          sq_nonneg ((x - 10) * (x - 40)), sq_nonneg ((x) * (x - 10)),
          sq_nonneg ((60 - 2 * x) / 2 - 10 * 2), sq_nonneg ((x / 10) - 1),
          sq_nonneg ((60 - 2 * x) / 40 - 1), sq_nonneg (x * (x - 30)), 
          sq_nonneg ((60 - 2 * x) * (x - 10)), sq_nonneg ((x - 0) * (30 - x)), sq_nonneg (x * (60 - 2 * x - 40)), 
          h, sq_nonneg (x * ((60 - 2 * x) - 40)), sq_nonneg ((x - 10) * ((60 - 2 * x) - 40))]