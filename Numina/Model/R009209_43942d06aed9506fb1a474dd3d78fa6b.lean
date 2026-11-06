import Mathlib

open Finset

theorem number_theory_609279 : ∑ k ∈ range 101, 2 ^ 100 / (2 ^ 50 + 2 ^ k) = 101 * 2 ^ 49 - 50 := by 
  native_decide