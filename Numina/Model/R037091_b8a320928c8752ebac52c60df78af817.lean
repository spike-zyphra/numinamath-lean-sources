import Mathlib

theorem number_theory_16737 : IsGreatest {p | p.Prime ∧ p ∣ Nat.factorial 12 + Nat.factorial 14} 61 := by
  constructor
  · -- Show 61 is in the set
    constructor
    · -- Show 61 is prime
      norm_num
    · -- Show 61 divides Nat.factorial 12 + Nat.factorial 14
      native_decide
  · -- Show there is no greater element in the set
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    by_contra h
    push_neg at h
    have h1 : p ≤ Nat.factorial 12 + Nat.factorial 14 := by
      exact Nat.le_of_dvd (by positivity) h_div
    have h2 : p ∣ Nat.factorial 12 + Nat.factorial 14 := h_div
    have h3 : Nat.factorial 12 + Nat.factorial 14 = (Nat.factorial 12) * 183 := by 
      calc
        Nat.factorial 12 + Nat.factorial 14 = Nat.factorial 12 + (14 * 13 * Nat.factorial 12) := by 
          rw [show Nat.factorial 14 = 14 * 13 * Nat.factorial 12 by native_decide]
          <;> ring_nf
        _ = Nat.factorial 12 * (1 + 14 * 13) := by 
          ring_nf
        _ = Nat.factorial 12 * 183 := by 
          norm_num
    rw [h3] at h2
    have h4 : p ∣ (Nat.factorial 12) ∨ p ∣ (183) := by 
      apply (Nat.Prime.dvd_mul h_prime).mp
      exact h2
    rcases h4 with (h4 | h4)
    · -- Case p divides Nat.factorial 12
      have h5 : p ≤ 12 := by
        exact (Nat.Prime.dvd_factorial h_prime).mp h4
      linarith
    · -- Case p divides 183
      have h41 : p ≤ 183 := by
        exact Nat.le_of_dvd (by norm_num) h4
      interval_cases p <;> norm_num at h_prime h4 h41 <;> try { contradiction }
      <;> omega