import Mathlib

def seq : ℕ → ℕ
| n => n^5 - n

theorem number_theory_102160 : IsGreatest {x | ∀ n, x ∣ seq n} 30 := by
  constructor 
  · -- First, show 30 is in the set; i.e., 30 divides all terms
    show ∀ n, 30 ∣ seq n
    intro n 
    have h1 : n ^ 5 % 2 = n % 2 := by 
      have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega 
      rcases h2 with (h2 | h2) 
      all_goals 
        simp [h2, Nat.pow_mod]
    have h2 : n ^ 5 % 3 = n % 3 := by 
      have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega 
      rcases h3 with (h3 | h3 | h3)
      all_goals 
        simp [h3, Nat.pow_mod]
    have h3 : n ^ 5 % 5 = n % 5 := by 
      have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4)
      all_goals 
        simp [h4, Nat.pow_mod]
    have h7 : (n ^ 5 - n) % 30 = 0 := by 
      omega
    exact Nat.dvd_of_mod_eq_zero h7
  · -- Now show 30 is greatest 
    intro x hx 
    have h1 : ∀ n, x ∣ seq n := hx 
    have h1_2 := h1 2
    have h2 : x ∣ 30 := by
      norm_num [seq] at h1_2 
      exact h1_2
    have h3 : x ≤ 30 := by 
      exact Nat.le_of_dvd (show 0 < 30 by norm_num) h2
    linarith