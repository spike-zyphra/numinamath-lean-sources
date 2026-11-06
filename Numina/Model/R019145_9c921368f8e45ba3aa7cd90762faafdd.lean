import Mathlib

open Finset Real

theorem algebra_170014 : ∏ i ∈ range 1009, (1 + 1 / ((2 * i + 2))) < 50 := by 
  native_decide