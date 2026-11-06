import Mathlib

theorem number_theory_184932 : (Nat.primeFactors 7999999999).card ≤ 2 →
    IsGreatest {p | p.Prime ∧ p ∣ 7999999999} 4002001 := by
  intro h
  constructor
  · -- Show 4002001 is in the set
    constructor
    · -- Show that 4002001 is prime
      norm_num
    · -- Show that 4002001 divides 7999999999
      norm_num
  · -- Show that 4002001 is greatest in the set
    intro p hp
    rcases hp with ⟨h_prime, hdiv⟩
    have h1 : p ∣ 7999999999 := hdiv
    have h2 : p ∣ 1999 ∨ p ∣ 4002001 := by
      have h4 : p ∣ 1999 * 4002001 := by
        norm_num at h1 ⊢
        exact h1
      have h5 : p ∣ 1999 ∨ p ∣ 4002001 := by
        apply (Nat.Prime.dvd_mul h_prime).mp
        exact h4
      exact h5
    rcases h2 with (h2 | h2)
    · -- Assume p divides 1999
      have h3 : p ∣ 1999 := h2
      have h4 : p ≤ 1999 := by 
        exact Nat.le_of_dvd (by norm_num) h3
      have h5 : p ≤ 4002001 := by 
        omega
      linarith
    · -- Assume p divides 4002001
      have h3 : p ∣ 4002001 := h2
      have h4 : p ≤ 4002001 := by 
        apply Nat.le_of_dvd (by norm_num) h3
      by_contra h
      push_neg at h
      have h5 : p > 4002001 := h
      have h6 : p ≤ 4002001 := by
        apply Nat.le_of_dvd (by norm_num) h3
      omega