import Mathlib

open Finset

def f (k : ℕ) := (Nat.digits 10 k).sum ^ 2

theorem number_theory_149187 : f^[1992] (2^1991) = 256 := by native_decide