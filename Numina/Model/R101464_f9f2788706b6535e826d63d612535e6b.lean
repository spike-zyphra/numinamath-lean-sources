import Mathlib

open Finset Real

theorem algebra_303979 : ∏ i ∈ range 1006, (1 - 1 / (∑ j ∈ range (i + 1), j + 1)) = 1007 / 3018 := by
  native_decide