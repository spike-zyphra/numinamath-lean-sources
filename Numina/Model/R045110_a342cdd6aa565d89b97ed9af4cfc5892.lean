import Mathlib

def P (n : ℕ) := (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9)

theorem number_theory_36917 :
  IsGreatest {k | ∀ n > 0, Even n → k ∣ P n} 15 := by 
  constructor 
  · -- Show that 15 is in the set
    show ∀ n > 0, Even n → 15 ∣ P n 
    intro n hn hneven 
    have h1 : n % 2 = 0 := by 
      rcases hneven with ⟨m, hm⟩ 
      omega 
    have h2 : (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) % 3 = 0 := by 
      have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega 
      rcases h3 with (h3 | h3 | h3) <;> simp [h3, Nat.mul_mod, Nat.add_mod] 
    have h3 : (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) % 5 = 0 := by 
      have h3 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega 
      rcases h3 with (h3 | h3 | h3 | h3 | h3) <;> simp [h3, Nat.mul_mod, Nat.add_mod] 
    have h4 : 15 ∣ (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) := by 
      omega 
    simp [P] at *
    all_goals try tauto
  · -- Show that 15 is the greatest 
    intro k hk 
    have h : ∀ n > 0, Even n → k ∣ P n := hk 
    have h4 := h 2 (by norm_num) (by decide)
    have h8 := h 8 (by norm_num) (by decide)
    have h16 := h 16 (by norm_num) (by decide)
    norm_num [P] at h4 h8 h16
    have h3 : k ∣ 15 := by 
      exact Nat.dvd_gcd (Nat.dvd_gcd h4 h8) h16
    have h7 : k ≤ 15 := by 
      exact Nat.le_of_dvd (by norm_num) h3 
    linarith