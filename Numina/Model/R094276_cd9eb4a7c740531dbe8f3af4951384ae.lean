import Mathlib

open Finset

theorem number_theory_327361 : (Nat.factorial 1 * ∏ i ∈ Icc 2 100, Nat.factorial i) % 10^1124 = 0 := by 
  native_decide