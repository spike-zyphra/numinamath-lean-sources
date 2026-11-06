import Mathlib

open Nat Nat.Prime

theorem number_theory_96996 : ∑ p in (2010 : ℕ).primeFactors, p = 77 := by 
  native_decide