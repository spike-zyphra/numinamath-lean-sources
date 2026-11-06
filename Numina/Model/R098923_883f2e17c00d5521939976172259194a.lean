import Mathlib

open Finset

theorem number_theory_2995 : (∑ i ∈ Icc 1 100, i^i) % 10 = 0 := by 
  native_decide