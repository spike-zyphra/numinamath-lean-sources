import Mathlib

open Real

theorem algebra_3303 : ∑ n in Finset.Icc 1 100, ((1 / (n ^ 2 + n)) - (1 / (n ^ 2 + 3 * n + 2))) = 20800 / 31209 := by
  native_decide