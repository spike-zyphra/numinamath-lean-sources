import Mathlib

open Finset

theorem algebra_215851 : ∑ i ∈ range 2021, (10^(i + 1) - 1) * 3 / 9 = (10^2022 - 18199) / 27 := by
  native_decide