import Mathlib

open Nat

theorem number_theory_14225 : IsLeast {p | Odd p ∧ Prime p ∧ p ∣ (2019^8 + 1)} 97 := by
  constructor
  · -- Show 97 is in the set
    constructor
    · -- Show 97 is odd
      exact Nat.odd_iff.mpr (by norm_num)
    constructor
    · -- Show 97 is prime
      norm_num
    · -- Show 97 divides 2019^8 + 1
      norm_num
  · -- Show there is no smaller element in the set
    intro p hp
    rcases hp with ⟨hodd, hprime, hdiv⟩
    by_contra h
    push_neg at h
    have h1 : p < 97 := by linarith
    interval_cases p <;> norm_num at hprime hdiv hodd ⊢ <;> all_goals contradiction