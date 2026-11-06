import Mathlib

open Nat

def start_with_10 (n : ℕ) := (digits 10 n).headI = 1 ∧ (digits 10 n).tail.headI = 0

theorem number_theory_8840 :
    ∃ n : ℕ, 0 < n ∧ start_with_10 (3^n) ∧ start_with_10 (7^n) := by
  use 20
  constructor
  · norm_num
  constructor
  · -- Show that 3^20 starts with 10
    unfold start_with_10
    constructor
    · -- Show that the first digit is 1
      norm_num [Nat.digits, Nat.digitsAux]
    · -- Show that the second digit is 0
      norm_num [Nat.digits, Nat.digitsAux]
  · -- Show that 7^20 starts with 10
    unfold start_with_10
    constructor
    · -- Show that the first digit is 1
      norm_num [Nat.digits, Nat.digitsAux]
    · -- Show that the second digit is 0
      norm_num [Nat.digits, Nat.digitsAux]