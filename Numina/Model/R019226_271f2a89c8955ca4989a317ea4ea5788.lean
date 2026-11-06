import Mathlib

open Finset Real

theorem algebra_322674 : ∏ i ∈ range 1006, ((2 * i + 2) ^ 4 + (2 * i + 2) ^ 2 + 1) /
    ((2 * i + 3) ^ 4 + (2 * i + 3) ^ 2 + 1) = 3 / 4054183 := by 
  native_decide