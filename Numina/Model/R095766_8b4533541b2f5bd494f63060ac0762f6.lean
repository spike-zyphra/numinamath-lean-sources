import Mathlib

theorem number_theory_14237 :
    IsLeast {p | p.Prime ∧ (Nat.digits 10 p).sum = 19} 199 := by
  constructor
  · -- Show 199 is in the set (i.e., it's prime and sum of digits is 19)
    constructor
    · -- Show 199 is prime
      norm_num
    · -- Show sum of digits is 19
      norm_num
  · -- Show there is no smaller element in the set
    intro p hp
    rcases hp with ⟨h_prime, h_sum⟩
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at h_prime h_sum <;> all_goals contradiction