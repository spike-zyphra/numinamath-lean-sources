import Mathlib

theorem number_theory_277969 : (Nat.Prime 13 ∧ Nat.Prime 31) := by 
  constructor
  · -- Show 13 is prime
    norm_num
  · -- Show 31 is prime
    norm_num