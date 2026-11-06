import Mathlib

open Finset

theorem algebra_612 : ⌊(1 / (∑ i ∈ Icc (1980 : ℤ) 1991, (1 : ℚ) / i))⌋ = 165 := by
  native_decide