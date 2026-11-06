import Mathlib

theorem number_theory_10824 {N : ℕ} (hN : N = ∑ d in (Nat.divisors 200), d) :
    IsGreatest {p | p.Prime ∧ p ∣ N} 31 := by
  have h1 : N = 465 := by 
    rw [hN]
    native_decide
  rw [h1] at *
  constructor
  · -- Show that 31 is indeed in the set
    constructor
    · -- Show that 31 is prime
      norm_num
    · -- Show that 31 divides 465
      norm_num
  · -- Show that 31 is greatest in the set
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    have h_le : p ≤ 465 := by 
      exact Nat.le_of_dvd (by norm_num) h_div
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at h_prime h_div <;> contradiction