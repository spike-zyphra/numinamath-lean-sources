import Mathlib

open Nat

def diamond (n m : ℕ) := (n * m).primeFactors.card

theorem number_theory_240719 : (diamond 720 1001)^3 = 216 := by
  native_decide