import Mathlib

theorem algebra_16558 {n : ℕ} (hn : n = 99) :
    IsGreatest {p | p.Prime ∧ p ∣ n} 11 := by 
  rw [hn]
  constructor
  · -- Show that 11 is in the set.
    constructor
    · -- Show that 11 is prime
      norm_num
    · -- Show that 11 divides 99
      norm_num
  · -- Show that 11 is greatest in the set
    intro p hp
    rcases hp with ⟨h_prime, hdiv⟩
    have h1 : p ≤ 99 := by
      exact Nat.le_of_dvd (by norm_num) hdiv
    by_contra h
    push_neg at h 
    interval_cases p <;> norm_num at h_prime hdiv <;> all_goals contradiction