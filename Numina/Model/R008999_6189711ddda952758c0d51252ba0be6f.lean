import Mathlib

open Nat

theorem number_theory_19466 : (∏ p in (Nat.primesBelow 100), p) % 16 = 6 := by
  native_decide