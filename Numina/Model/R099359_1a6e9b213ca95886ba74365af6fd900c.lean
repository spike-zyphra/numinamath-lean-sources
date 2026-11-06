import Mathlib

open Real
open scoped BigOperators

theorem algebra_9407 : ∑ i ∈ Finset.range 2004, (i + 1) / (Nat.factorial i + Nat.factorial (i + 1) + Nat.factorial (i + 2)) = 1 / 2 - 1 / Nat.factorial 2004 := by
  native_decide