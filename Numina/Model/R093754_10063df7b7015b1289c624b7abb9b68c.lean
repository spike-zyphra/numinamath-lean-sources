import Mathlib

theorem number_theory_271307 :
    (Nat.digits 10 (6^811)).headI = 6 ∧
    (Nat.digits 10 (2^1000)).headI = 6 ∧
    (Nat.digits 10 (3^999)).headI = 7 := by
  native_decide