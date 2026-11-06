import Mathlib

open Finset

def sumOfPowerset (n : ℕ) := ∑ i ∈ range (n + 1), (3^i)

theorem number_theory_6874 : (sumOfPowerset 888) % 10 = 1 := by 
  native_decide