import Mathlib

open Finset Real

theorem algebra_170742 : ∑ n ∈ Icc 2 17, (n^2 + n + 1) / (n^4 + 2 * n^3 - n^2 - 2 * n) = 592 / 969 := by 
  native_decide