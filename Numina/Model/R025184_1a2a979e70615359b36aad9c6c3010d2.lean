import Mathlib

open Finset Real

theorem algebra_284325 : ∑ i ∈ range 1001, (1 / ((2 * i + 1) * (2 * i + 3) * (2 * i + 5))) = 1004003 / 12048045 := by 
  native_decide