import Mathlib

open Finset

theorem algebra_220553 : (∑ i ∈ range 2020, (1 / (∑ j ∈ range (i + 1), (j + 1)))) / 2 = 2020 / 2021 := by
  native_decide