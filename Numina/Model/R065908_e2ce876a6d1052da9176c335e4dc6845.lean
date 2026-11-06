import Mathlib

theorem number_theory_136173 (p : ℕ) (hp : Nat.Prime p) (h : Nat.Prime (p + 2)) :
    p = 3 ∨ 6 ∣ (p + 1) := by
  by_cases h1 : p ≤ 5
  · interval_cases p <;> norm_num at hp h ⊢ 
    <;> try { tauto }
    <;> try { 
      native_decide
    }
    <;> try { contradiction }
  · -- Assume p > 5, we need to show 6 divides p + 1
    push_neg at h1
    have h2 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · -- Case p ≡ 0 [MOD 3]
      have h3 : p % 3 = 0 := by tauto
      have h4 : 3 ∣ p := by
        omega
      have h5 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt h4
        all_goals 
          omega
      contradiction
    · -- Case p ≡ 1 [MOD 3]
      have h3 : (p + 2) % 3 = 0 := by 
        omega
      have h4 : 3 ∣ (p + 2) := by
        omega
      have h5 : ¬ Nat.Prime (p + 2) := by
        apply Nat.not_prime_of_dvd_of_lt h4
        all_goals 
          omega
      contradiction
    · -- Case p ≡ 2 [MOD 3]
      have h3 : (p + 1) % 3 = 0 := by 
        omega
      have h4 : p % 2 = 1 := by
        by_contra h2'
        push_neg at h2'
        have h2'' : 2 ∣ p := by
          omega
        have h3' : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt h2''
          all_goals
            omega
        contradiction
      have h5 : (p + 1) % 2 = 0 := by 
        omega
      have h6 : 6 ∣ (p + 1) := by
        omega
      right
      exact h6