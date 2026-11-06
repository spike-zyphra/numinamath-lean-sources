import Mathlib
open Polynomial

theorem algebra_16798 : ((C 2 * X ^ 4 + C 3 * X ^ 3 + X - C 14 : ℝ[X]) * (C 3 * X ^ 10 - C 9 * X ^ 7 + C 9 * X ^ 4 + C 30) - (X ^ 2 + C 5) ^ 7).degree = 14 := by
  compute_degree!
  <;> norm_num
  <;> try native_decide