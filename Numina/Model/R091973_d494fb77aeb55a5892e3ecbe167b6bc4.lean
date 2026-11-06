import Mathlib

theorem number_theory_103501 (p : ℕ) (hp : p.Prime) (h : (p ^ 2 + 2).Prime) :
    (p ^ 3 + 2).Prime := by 
  by_cases h3 : p ≤ 3
  · -- If p ≤ 3, then it must be 2 or 3.
    interval_cases p <;> norm_num at hp h ⊢ <;> tauto <;> norm_num
    <;> try tauto
  · -- Assume p > 3.
    have h4 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h4 with (h4 | h4 | h4)
    · -- Assume p ≡ 0 (mod 3).
      have h6 : p % 3 = 0 := by
        omega
      have h7 : ¬ p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals
          omega
      contradiction 
    · -- Assume p ≡ 1 (mod 3).
      have h5 : p % 3 = 1 := by
        omega
      have : ((p)^2 + 2) % 3 = 0 := by
        have hp2 : (p) ^ 2 % 3 = 1 := by
          have h7 : p % 3 = 1 := h5
          have : p ^ 2 % 3 = 1 := by
            simp [Nat.pow_mod, h7]
          exact this
        omega
      have h8 : 3 ∣ (p^2 + 2) := by 
        omega 
      have h9 : ¬ ((p)^2 + 2).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt h8 
        all_goals 
          nlinarith 
      contradiction 
    · -- Assume p ≡ 2 (mod 3).
      have h5 : p % 3 = 2 := by
        omega
      have : ((p)^2 + 2) % 3 = 0 := by
        have hp2 : (p) ^ 2 % 3 = 1 := by
          have h7 : p % 3 = 2 := h5
          have : p ^ 2 % 3 = 1 := by
            simp [Nat.pow_mod, h7]
          exact this
        omega
      have h8 : 3 ∣ (p^2 + 2) := by 
        omega 
      have h9 : ¬ ((p)^2 + 2).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt h8 
        all_goals 
          nlinarith 
      contradiction
  <;> norm_num 
  <;> try { contradiction }
  <;> norm_num
  <;> try { contradiction }
  <;> norm_num
  <;> try { contradiction }
  <;> norm_num 
  <;> try { contradiction }
  <;> norm_num
  <;> try { contradiction }
  all_goals try { norm_num at hp h ⊢ <;> tauto }
  all_goals try { contradiction }
  all_goals try { norm_num at hp h ⊢ <;> try { contradiction } <;> try { tauto } }