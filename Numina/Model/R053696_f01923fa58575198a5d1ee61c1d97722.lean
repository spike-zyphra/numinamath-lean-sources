import Mathlib

theorem number_theory_198871 :
    (Nat.digits 10 (2^1000))[0]! = 6 ∧
    (Nat.digits 10 (3^1000))[0]! = 1 ∧
    (Nat.digits 10 (7^1000))[0]! = 1 := by
  native_decide