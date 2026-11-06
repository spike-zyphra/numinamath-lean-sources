import Mathlib

theorem number_theory_12529 : IsGreatest {x | ∀ n : ℕ, 0 < n → Even n → x ∣ (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9)} 15 := by 
  constructor
  · -- Show that 15 is in the set
    show ∀ n : ℕ, 0 < n → Even n → 15 ∣ (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9)
    intro n hn hneven
    have h2 : (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) % 3 = 0 := by
      have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
        omega 
      rcases h3 with (h3 | h3 | h3)
      all_goals 
        simp [Nat.mul_mod, Nat.add_mod, h3]
    have h3 : (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) % 5 = 0 := by 
      have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
        omega 
      rcases h4 with (h4 | h4 | h4 | h4 | h4) 
      all_goals 
        simp [Nat.mul_mod, Nat.add_mod, h4]
    omega 
  · -- Show that 15 is greatest in the set 
    intro x hx 
    have h1 : ∀ n : ℕ, 0 < n → Even n → x ∣ (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) := hx 
    have h2 := h1 2 (by norm_num) (by decide)
    have h3 := h1 8 (by norm_num) (by decide)
    have h4 := h1 16 (by norm_num) (by decide)
    have h5 := h1 16 (by norm_num) (by decide)
    have h11 : x ∣ 15 := by 
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h2 h3) h4) h5
    have h7 : x ≤ 15 := by
      exact Nat.le_of_dvd (by norm_num) h11
    linarith