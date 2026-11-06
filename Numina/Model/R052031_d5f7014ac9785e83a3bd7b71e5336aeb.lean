import Mathlib

open Finset

theorem algebra_6465 : (∑ n ∈ Icc 1 672, ∏ i ∈ Icc 1 n, (3 * i - 1) / (3 * i + 3)) = 672 / 999 := by 
  native_decide