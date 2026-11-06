import Mathlib

open Finset Real

theorem algebra_132090 : ∑ i ∈ range 2008, (2 / ((i + 1) * (i + 2) * (i + 3))) = 1009522 / 2019045 := by
  native_decide