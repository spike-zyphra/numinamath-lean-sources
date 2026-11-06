import Mathlib

theorem number_theory_34075 (p : ℕ) (hp : Nat.Prime p) :
    ¬∃ n, n ≠ 0 ∧ n ≠ 1 ∧ ¬Nat.Prime n ∧ p % 30 = n := by 
  rintro ⟨n, hn1, hn2, hn3, h1⟩
  have h2 : n < 30 := by
    omega
  interval_cases n <;> norm_num at hn3 h1 ⊢
  all_goals 
    try { 
      norm_num at hn1 hn2 hn3 h1 ⊢ 
    }
  all_goals
    try { 
      have h3' : p % 2 = 0 := by
        omega 
      have h4' : ¬Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega) 
      contradiction
    }
  all_goals
    try { 
      have h3' : p % 3 = 0 := by
        omega 
      have h4' : ¬Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega) 
      contradiction
    }
  all_goals
    try { 
      have h3' : p % 5 = 0 := by
        omega 
      have h4' : ¬Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega) (by omega) (by omega) 
      contradiction
    }
  all_goals
    try { 
      have h3' : p % 2 = 0 := by 
        omega 
      have h4' : ¬Nat.Prime p := by 
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega) 
      contradiction 
    }