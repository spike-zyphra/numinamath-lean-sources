import Mathlib

open Finset

theorem number_theory_224736 : (∏ i ∈ Icc 2 2019, if i % 2 = 0 then (Nat.factorial i + 2) else (Nat.factorial i + 3)) % 10 = 8 := by
  native_decide