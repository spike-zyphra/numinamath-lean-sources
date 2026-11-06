import Mathlib

open Nat

theorem number_theory_93179 : ¬ Nat.Prime (202101) ∧ ¬ Nat.Prime (202103) ∧ ¬ Nat.Prime (202105)
    ∧ ¬ Nat.Prime (202107) := by 
  constructor
  · -- Show that 202101 is not prime
    norm_num [Nat.Prime]
  constructor
  · -- Show that 202103 is not prime
    norm_num [Nat.Prime]
  constructor
  · -- Show that 202105 is not prime
    norm_num [Nat.Prime]
  · -- Show that 202107 is not prime
    norm_num [Nat.Prime]