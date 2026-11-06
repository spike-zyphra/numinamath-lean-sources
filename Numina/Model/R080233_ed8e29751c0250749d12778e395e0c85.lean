import Mathlib

open Real

theorem algebra_216751 : ∑ i ∈ Finset.range 670, (1 / ((3 * i + 2) * (3 * i + 5))) = 335 / 2012 := by
  native_decide