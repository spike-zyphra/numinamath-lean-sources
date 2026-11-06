import Mathlib

theorem number_theory_36365 (p : ℕ) (hp : p.Prime) (hp2 : (p ^ 2 + 2).Prime) :
    {q | q.Prime ∧ q ∣ (p ^ 3 + 3)}.encard ≤ 3 := by
  by_cases h : p ≤ 3
  · interval_cases p <;> norm_num at hp hp2 ⊢ 
    <;> try { 
      have : {q | q.Prime ∧ q ∣ (30)} = {2, 3, 5} := by
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
        constructor
        · -- Assume q is prime and divides 30
          intro h
          rcases h with ⟨hq1, hq2⟩
          have h2 : q ≤ 30 := by
            by_contra h
            push_neg at h
            have h3 : q > 30 := h
            have h4 : q ∣ 30 := hq2
            have h5 : q ≤ 30 := by
              exact Nat.le_of_dvd (by norm_num) h4
            linarith
          interval_cases q <;> norm_num at hq1 hq2 ⊢
          <;> try tauto 
        · -- Assume q is in {2, 3, 5}
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
      rw [this]
      rw [Set.encard]
      simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
      <;> try { tauto }
    }
  · -- Assume p > 3
    have h2 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by 
      omega 
    rcases h2 with (h2 | h2 | h2)
    · -- Assume p ≡ 0 (mod 3)
      have h3 : p > 3 := by
        omega
      have h4 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) 
        all_goals 
          omega 
      contradiction 
    · -- Assume p ≡ 1 (mod 3)
      have h2' : (p ^ 2 + 2) % 3 = 0 := by 
        have h4 : p % 3 = 1 := h2 
        have : p ^ 2 % 3 = 1 := by 
          simp [Nat.pow_mod, h4] 
        omega 
      have h4 : ¬(p ^ 2 + 2).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p ^ 2 + 2) by omega) 
        all_goals 
          nlinarith [show p ≥ 4 by omega, show p ^ 2 + 2 ≥ 4 by nlinarith]
      contradiction 
    · -- Assume p ≡ 2 (mod 3)
      have h2' : (p ^ 2 + 2) % 3 = 0 := by 
        have h4 : p % 3 = 2 := h2 
        have : p ^ 2 % 3 = 1 := by 
          simp [Nat.pow_mod, h4] 
        omega 
      have h4 : ¬(p ^ 2 + 2).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p ^ 2 + 2) by omega) 
        all_goals 
          nlinarith [show p ≥ 4 by omega, show p ^ 2 + 2 ≥ 4 by nlinarith]
      contradiction