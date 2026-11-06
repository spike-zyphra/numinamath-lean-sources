import Mathlib

theorem number_theory_244735 : IsGreatest {p | p.Prime ∧ p ∣ (106^2 - 15^2)} 13 := by 
  constructor
  · -- Show 13 is in the set
    constructor
    · -- Show 13 is prime
      norm_num
    · -- Show 13 divides 106^2 - 15^2
      norm_num
  · -- Show there is no greater element in the set
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    norm_num at h_div
    by_contra h
    push_neg at h
    -- Assume p is a prime dividing 11011 with p > 13
    -- We need to derive a contradiction
    have h_le : p ≤ 11011 := by
      exact Nat.le_of_dvd (by norm_num) h_div
    interval_cases p <;> norm_num at h_prime h_div <;> try { contradiction }