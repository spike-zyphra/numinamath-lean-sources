import Mathlib

open Real

theorem algebra_5458 : ∏ i ∈ Finset.range 1001, (1 / (i + 1) + 1 / (2002 - i)) = 2003 ^ 1001 / Nat.factorial 2002 := by
  native_decide