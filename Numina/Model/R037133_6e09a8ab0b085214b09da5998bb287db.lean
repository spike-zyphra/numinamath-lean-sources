import Mathlib

open Nat

theorem number_theory_97759 : IsLeast {p | Odd p ∧ Prime p ∧ p ∣ 2019^8 + 1} 97 := by 
  constructor
  · -- Show 97 is indeed in the set
    constructor
    · -- Show 97 is odd
      exact Nat.odd_iff.mpr (by norm_num)
    constructor
    · -- Show 97 is prime
      norm_num
    · -- Show 97 divides 2019^8 + 1
      norm_num
  · -- Show no smaller element is in the set
    intro p hp
    rcases hp with ⟨h_odd, h_prime, h_div⟩
    by_contra h
    push_neg at h
    have h_le : p < 97 := by linarith
    interval_cases p <;> norm_num at h_prime h_odd h_div <;> contradiction