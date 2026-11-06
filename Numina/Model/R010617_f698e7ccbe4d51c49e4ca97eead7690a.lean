import Mathlib

open Finset

theorem number_theory_80434 : (Nat.digits 10 (∑ i ∈ range 321, (10^(i + 1) - 1))).sum = 342 := by
  native_decide