import Mathlib

open Finset

def f (n : ℕ) := (Nat.digits 10 (n ^ 2 + 1)).sum

theorem number_theory_294528 : f^[100] 1990 = 11 := by
  native_decide