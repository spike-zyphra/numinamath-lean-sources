import Mathlib

theorem number_theory_4484 :
    Nat.Prime 101 ∧ Nat.Prime 103 ∧ Nat.Prime 107 ∧
    ¬Nat.Prime 111 ∧ Nat.Prime 113 ∧ ¬Nat.Prime 121:= by 
  native_decide