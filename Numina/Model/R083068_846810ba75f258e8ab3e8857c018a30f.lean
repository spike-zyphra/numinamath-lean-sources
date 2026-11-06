import Mathlib

open Real
open scoped BigOperators

theorem algebra_22235 : ∑ i ∈ Finset.range 99, (1 / ((i + 1) * (i + 2))) = 99 / 100 := by
  native_decide