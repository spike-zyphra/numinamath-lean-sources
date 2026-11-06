import Mathlib

theorem number_theory_97225 : (Nat.digits 10 ((Nat.factorial 20) - (Nat.factorial 15))).length ≥ 3 ∧
    (Nat.digits 10 ((Nat.factorial 20) - (Nat.factorial 15)))[2]! = 0 := by
  native_decide