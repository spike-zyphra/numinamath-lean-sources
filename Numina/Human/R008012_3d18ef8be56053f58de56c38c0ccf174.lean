import Mathlib

theorem number_theory_274831 : (Nat.digits 10 (47^100)).length = 168 →
    (Nat.digits 10 (47^17)).length = 29 := by 
  intro h
  native_decide