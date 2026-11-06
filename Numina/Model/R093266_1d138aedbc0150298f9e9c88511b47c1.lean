import Mathlib

open Finset

def f (n : ℕ) := (Nat.digits 10 n).sum ^ 2 + (n % 3) + 1

theorem number_theory_210175 : f^[1990] 2345 = 3 := by
  native_decide