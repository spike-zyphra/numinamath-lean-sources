import Mathlib

theorem number_theory_15438 :
    IsLeast {n | (Nat.digits 10 n).length = 2 ∧ (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)) + 3) = 2 * n} 12 := by 
  constructor
  · -- Show 12 is in the set
    constructor
    · -- Show that 12 is 2-digit
      norm_num
    · -- Show that reversing 12's digits (to get 21) and then adding 3 results in 24, which is 2*12
      native_decide
  · -- Show 12 is the smallest
    intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h1 h2 <;> all_goals contradiction