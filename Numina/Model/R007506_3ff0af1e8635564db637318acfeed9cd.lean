import Mathlib

theorem algebra_12290 :
    IsLeast {p | p.Prime ∧ (Nat.digits 10 p).length = 2 ∧ ¬(Nat.Prime (Nat.ofDigits 10 (List.reverse (Nat.digits 10 p))))} 19 := by
  constructor
  · -- Show that 19 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    · native_decide
  · -- Show that 19 is the smallest in the set
    intro p hp
    rcases hp with ⟨h_prime, h_length, h_not_prime⟩
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at *
    all_goals contradiction