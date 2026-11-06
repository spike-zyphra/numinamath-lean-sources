import Mathlib

theorem number_theory_200380 : {p : ℕ | p.Prime ∧ p ∣ 15147}.encard = 3 := by
  have h1 : {p : ℕ | p.Prime ∧ p ∣ 15147} = {3, 11, 17} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume h : p is prime and divides 15147
      intro h
      rcases h with ⟨h_prime, h_div⟩
      have h2 : p ≤ 15147 := by
        exact Nat.le_of_dvd (by norm_num) h_div
      by_cases h3 : p ≤ 17
      · interval_cases p <;> norm_num at h_prime h_div ⊢ <;> tauto
      · -- Case p > 17, but given that p divides 15147, which factors as 3^4*11*17.
        push_neg at h3
        have h4 : p ∣ 15147 := h_div
        have h5 : p ≤ 15147 := h2
        have h6 : p ∣ 3 ^ 4 * 11 * 17 := by 
          norm_num at h4 ⊢
          exact h4
        have h7 : p ∣ 3 ^ 4 ∨ p ∣ 11 ∨ p ∣ 17 := by 
          have h8 : p ∣ 3 ^ 4 * 11 ∨ p ∣ 17 := by 
            apply (Nat.Prime.dvd_mul h_prime).mp
            exact h6
          cases h8 with 
          | inl h9 =>
            have h10 : p ∣ 3 ^ 4 ∨ p ∣ 11 := by 
              apply (Nat.Prime.dvd_mul h_prime).mp
              exact h9
            cases h10 with 
            | inl h11 => exact Or.inl h11
            | inr h12 => exact Or.inr (Or.inl h12)
          | inr h9 => exact Or.inr (Or.inr h9)
        cases h7 with
        | inl h8 =>
          -- p divides 3^4 and is prime, therefore p = 3
          have h_eq3 : p = 3 := by 
            have h9 : p ∣ 3 := by
              have h10 : p ∣ 3 ^ 4 := h8
              exact Nat.Prime.dvd_of_dvd_pow h_prime h10
            have h2_prime : p ≤ 3 := by 
              exact Nat.le_of_dvd (by linarith) h9
            interval_cases p <;> norm_num at h_prime h9 h2_prime ⊢ <;> tauto
          rw [h_eq3]
          all_goals norm_num
          <;> tauto
        | inr h_eq11_or_17 =>
          cases h_eq11_or_17 with 
          | inl h_eq11 =>
            -- p divides 11 and is prime, therefore p = 11
            have h_eq11' : p = 11 := by 
              have h11 : p ∣ 11 := h_eq11
              have h2_prime11 : p ≤ 11 := by 
                exact Nat.le_of_dvd (by linarith) h11
              interval_cases p <;> norm_num at h_prime h11 h2_prime11 ⊢ <;> tauto
            rw [h_eq11']
            all_goals norm_num
            <;> tauto
          | inr h_eq17 =>
            -- p divides 17 and is prime, therefore p = 17
            have h_eq17' : p = 17 := by 
              have h17 : p ∣ 17 := h_eq17
              have h2_prime17 : p ≤ 17 := by 
                exact Nat.le_of_dvd (by linarith) h17
              interval_cases p <;> norm_num at h_prime h17 h2_prime17 ⊢ <;> tauto
            rw [h_eq17']
            all_goals norm_num
            <;> tauto
    · -- Show that each prime in {3, 11, 17} divides 15147
      rintro (rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals omega
  all_goals try { try { trivial } }