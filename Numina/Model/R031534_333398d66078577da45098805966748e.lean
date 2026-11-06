import Mathlib

theorem algebra_13275 : IsGreatest {p | Nat.Prime p ∧ p ∣ (25^2 + 72^2)} 157 := by 
  constructor
  · -- Show 157 is in the set.
    constructor
    · -- Show 157 is prime.
      norm_num
    · -- Show 157 divides 25^2 + 72^2.
      norm_num
  · -- Show that 157 is greatest in the set.
    intro p hp
    rcases hp with ⟨h_prime, hdiv⟩
    norm_num at hdiv
    by_contra h
    push_neg at h
    have h1 : p ≤ 5809 := by 
      exact Nat.le_of_dvd (show 0 < 5809 by norm_num) hdiv
    interval_cases p <;> norm_num at h_prime hdiv <;> all_goals contradiction