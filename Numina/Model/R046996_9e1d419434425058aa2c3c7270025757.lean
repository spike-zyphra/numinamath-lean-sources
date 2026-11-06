import Mathlib

theorem number_theory_37594 : IsGreatest {p | p.Prime ∧ p ∣ 1000^2 - 950^2} 13 := by
  constructor
  · -- Show that 13 is in the set.
    constructor
    · -- Show that 13 is prime
      norm_num
    · -- Show that 13 divides 1000^2 - 950^2
      norm_num
  · -- Show that 13 is greatest in the set.
    intro p hp
    rcases hp with ⟨h_prime, hdiv⟩
    norm_num at hdiv
    by_contra h
    push_neg at h
    have h4 : p ∣ 97500 := hdiv
    have h5 : p ≤ 97500 := by
      exact Nat.le_of_dvd (by norm_num) h4
    have h6 : p ∣ 97500 := hdiv
    have h7 : p ∣ 2 ^ 2 * 3 * 5 ^ 4 * 13 := by
      norm_num at h6 ⊢
      all_goals try exact h6
    have h8 : p ∣ 2 ^ 2 * 3 * 5 ^ 4 * 13 := h7
    have h9 : p ≤ 13 := by
      have h10 : p ∣ 2 ^ 2 * 3 * 5 ^ 4 * 13 := h8
      have h11 : p ∣ 2 ^ 2 ∨ p ∣ 3 ∨ p ∣ 5 ^ 4 ∨ p ∣ 13 := by
        have h12 : p ∣ 2 ^ 2 * 3 * 5 ^ 4 * 13 := h10
        have h13 : p ∣ (2 ^ 2 * (3 * (5 ^ 4 * 13))) := by
          simpa using h12
        have h14 : p ∣ 2 ^ 2 ∨ p ∣ (3 * (5 ^ 4 * 13)) := (Nat.Prime.dvd_mul h_prime).1 h13
        rcases h14 with (h | h)
        · -- Case p divides 2^2
          tauto
        · -- Case p divides 3 * (5^4 * 13)
          have h18 : p ∣ 3 ∨ p ∣ (5 ^ 4 * 13) := by
            have h19 : p ∣ 3 * (5 ^ 4 * 13) := by
              simpa using h
            have h20 : p ∣ 3 ∨ p ∣ (5 ^ 4 * 13) := (Nat.Prime.dvd_mul h_prime).1 h19
            exact h20
          rcases h18 with (h | h)
          · -- Case p divides 3
            tauto
          · -- Case p divides 5^4 * 13
            have h16 : p ∣ 5 ^ 4 ∨ p ∣ 13 := by
              have h17 : p ∣ 5 ^ 4 * 13 := by
                simpa using h
              have h18 : p ∣ 5 ^ 4 ∨ p ∣ 13 := (Nat.Prime.dvd_mul h_prime).1 h17
              exact h18
            tauto
      rcases h11 with (h | h | h | h)
      · -- Case p divides 2 ^ 2
        have h15 : p ∣ 2 := by
          have h16 : p ∣ 2 ^ 2 := h
          have h17 : p ∣ 2 := by
            exact Nat.Prime.dvd_of_dvd_pow h_prime h16
          exact h17
        have h18 : p ≤ 2 := by
          exact Nat.le_of_dvd (by norm_num) h15
        omega
      · -- Case p divides 3
        have h15 : p ∣ 3 := h
        have h18 : p ≤ 3 := by
          exact Nat.le_of_dvd (by norm_num) h15
        omega
      · -- Case p divides 5 ^ 4
        have h17 : p ∣ 5 := by
          have h18 : p ∣ 5 ^ 4 := h
          have h19 : p ∣ 5 := by
            exact Nat.Prime.dvd_of_dvd_pow h_prime h18
          exact h19
        have h18 : p ≤ 5 := by
          exact Nat.le_of_dvd (by norm_num) h17
        omega
      · -- Case p divides 13
        have h18 : p ∣ 13 := h
        have h19 : p ≤ 13 := by
          exact Nat.le_of_dvd (by norm_num) h18
        omega
    linarith