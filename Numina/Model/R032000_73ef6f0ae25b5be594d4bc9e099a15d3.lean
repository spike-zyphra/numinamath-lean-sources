import Mathlib

theorem number_theory_5784 {n : ℕ} (hn : n = 2^13 + 2^11 - 10) :
    IsGreatest {p | p.Prime ∧ p ∣ n} 31 := by
  rw [hn]
  constructor
  · -- Show 31 is in the set.
    constructor
    · -- Show 31 is prime.
      norm_num
    · -- Show 31 divides $2^{13} + 2^{11} - 10$.
      norm_num
  · -- Show there is no larger element in the set.
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    have h3 : p ∣ 10230 := h_div
    have h4 : p ≤ 10230 := by
      exact Nat.le_of_dvd (by norm_num) h3
    by_contra h
    push_neg at h
    -- Let's show that any prime dividing 10230 is at most 31.
    -- From our previous factorization: 10230 = 2 × 3 × 5 × 11 × 31
    -- So the prime factors are 2, 3, 5, 11, and 31. The largest is 31.
    have h6 : p ∣ 2 * 3 * 5 * 11 * 31 := by
      have h7 : (2 * 3 * 5 * 11 * 31 : ℕ) = 10230 := by norm_num
      rw [h7] at *
      exact h3
    -- Since p is a prime dividing a product, it divides one of the factors.
    have h8 : p ∣ 2 ∨ p ∣ 3 * 5 * 11 * 31 := by
      apply (Nat.Prime.dvd_mul h_prime).mp
      simpa using h6
    rcases h8 with h9 | h10
    · -- p divides 2
      have h11 : p ≤ 2 := by
        exact Nat.le_of_dvd (by norm_num) h9
      nlinarith
    · -- p divides 3 * 5 * 11 * 31
      have h13 : p ∣ 3 * 5 * 11 * 31 := h10
      have h14 : p ∣ 3 ∨ p ∣ 5 * 11 * 31 := by
        apply (Nat.Prime.dvd_mul h_prime).mp
        simpa using h13
      rcases h14 with h15 | h16
      · -- p divides 3
        have h17 : p ≤ 3 := by
          exact Nat.le_of_dvd (by norm_num) h15
        nlinarith
      · -- p divides 5 * 11 * 31
        have h19 : p ∣ 5 * 11 * 31 := h16
        have h20 : p ∣ 5 ∨ p ∣ 11 * 31 := by
          apply (Nat.Prime.dvd_mul h_prime).mp
          simpa using h19
        rcases h20 with h21 | h22
        · -- p divides 5
          have h23 : p ≤ 5 := by
            exact Nat.le_of_dvd (by norm_num) h21
          nlinarith
        · -- p divides 11 * 31
          have h24 : p ∣ 11 * 31 := h22
          have h25 : p ∣ 11 ∨ p ∣ 31 := by
            apply (Nat.Prime.dvd_mul h_prime).mp
            simpa using h24
          rcases h25 with h26 | h27
          · -- p divides 11
            have h28 : p ≤ 11 := by
              exact Nat.le_of_dvd (by norm_num) h26
            nlinarith
          · -- p divides 31
            have h29 : p ≤ 31 := by
              exact Nat.le_of_dvd (by norm_num) h27
            nlinarith