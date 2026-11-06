import Mathlib

open Finset

def f (k : ℕ) := (Nat.digits 10 k).sum ^ 2

theorem number_theory_286478 : f^[1991] (2^1990) = 256 := by
  native_decide