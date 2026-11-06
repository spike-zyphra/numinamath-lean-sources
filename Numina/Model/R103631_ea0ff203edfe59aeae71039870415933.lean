import Mathlib

open Finset

def f (k : ℕ) := (Nat.digits 10 k).sum ^ 2

theorem number_theory_179885 : f^[2005] (2^2006) = 169 := by native_decide