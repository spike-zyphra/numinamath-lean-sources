import Mathlib

open Finset

theorem number_theory_234360 : ∑ i ∈ range 2018, (10^(i + 1) - 1) * 6 / 9 = 2 * (10^2019 - 18172) / 27 := by 
  native_decide