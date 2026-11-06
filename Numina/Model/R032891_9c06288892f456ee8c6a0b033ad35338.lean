import Mathlib

theorem number_theory_16085 : IsGreatest {p | p.Prime ∧ p ∣ (15^3 + 10^4 - 5^5)} 41 := by
  constructor
  · -- Show 41 is in that set
    constructor
    · -- Show 41 is prime
      norm_num 
    · -- Show 41 divides $15^3 + 10^4 - 5^5$
      norm_num 
  · -- Show that if $p \in \{p | p.Prime \land p \mid (15^3 + 10^4 - 5^5)\}$, then $p \le 41$.
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    have h1 : p ∣ 10250 := by 
      exact_mod_cast h_div
    have h3 : p ≤ 41 := by 
      by_contra h 
      push_neg at h 
      have h4 : p ∣ 10250 := h1 
      have h5 : p ≥ 42 := by
        omega
      have h6 : p ∣ 2 * (5 ^ 3 * 41) := by 
        norm_num at h4 ⊢ 
        exact_mod_cast h4 
      have h7 : p ∣ 2 ∨ p ∣ (5 ^ 3 * 41) := by 
        apply (Nat.Prime.dvd_mul h_prime).mp 
        exact h6 
      rcases h7 with (h8 | h9)
      · -- Case p ∣ 2
        have h8' : p ∣ 2 := h8 
        have : p ≤ 2 := by 
          exact Nat.le_of_dvd (by norm_num) h8' 
        omega 
      · -- Case p ∣ (5 ^ 3 * 41)
        have h9' : p ∣ (5 ^ 3 * 41) := h9 
        have h10 : p ∣ 5 ^ 3 ∨ p ∣ 41 := by 
          apply (Nat.Prime.dvd_mul h_prime).mp 
          exact h9' 
        rcases h10 with (h11 | h12)
        · -- Case p ∣ 5^3 
          have h11' : p ∣ 5 ^ 3 := h11 
          have : p ≤ 5 ^ 3 := by 
            exact Nat.le_of_dvd (by norm_num) h11' 
          have : p ∣ 5 := by 
            have h9 : p ∣ 5 ^ 3 := by exact_mod_cast h11
            have h11 : p ∣ 5 ^ 3 := h9
            have h11 : p ∣ 5 := by 
                exact Nat.Prime.dvd_of_dvd_pow h_prime (show p ∣ 5 ^ 3 by exact_mod_cast h11) 
            exact_mod_cast h11 
          have : p ≤ 5 := by 
            exact Nat.le_of_dvd (by norm_num) this 
          omega 
        · -- Case p ∣ 41
          have h12' : p ∣ 41 := h12 
          have : p = 41 := by 
            have : p ∣ 41 := by 
              exact_mod_cast h12 
            have h6 : p ≤ 41 := by 
              exact Nat.le_of_dvd (by norm_num) this 
            interval_cases p <;> try { contradiction }
            <;> try tauto 
          omega
    exact_mod_cast h3