import Mathlib

theorem number_theory_4839 :
    IsGreatest {n : ℕ | 0 < n ∧ ∀ p q : ℕ, p.Prime ∧ q.Prime → p > 3 → q > 3 → n ∣ p ^ 4 - q ^ 4} 48 := by 
  constructor
  · -- Show that 48 is in the set 
    constructor 
    · -- Show 0 < 48
      norm_num 
    · intro p q hpq hp hq
      have h1 : p > 3 := hp
      have h2 : q > 3 := hq
      have hp1 : p % 2 = 1 := by
        by_contra h
        push_neg at h
        have : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
        have h3 : p.Prime := (hpq).left
        contradiction
      have hq1 : q % 2 = 1 := by
        by_contra h
        push_neg at h
        have : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by omega) (by omega)
        have h4 : q.Prime := (hpq).right
        contradiction
      have h3 : p ^ 4 % 16 = 1 := by
        have h1 : p % 2 = 1 := hp1
        have h2 : p % 16 = 1 ∨ p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 11 ∨ p % 16 = 13 ∨ p % 16 = 15 := by
          omega
        rcases h2 with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
      have h4 : q ^ 4 % 16 = 1 := by
        have h1 : q % 2 = 1 := hq1
        have h2 : q % 16 = 1 ∨ q % 16 = 3 ∨ q % 16 = 5 ∨ q % 16 = 7 ∨ q % 16 = 9 ∨ q % 16 = 11 ∨ q % 16 = 13 ∨ q % 16 = 15 := by
          omega
        rcases h2 with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
      have h5 : (p ^ 4 - q ^ 4) % 16 = 0 := by
        omega 
      have h6 : (p ^ 4 - q ^ 4) % 3 = 0 := by
        have h7 : p % 3 = 1 ∨ p % 3 = 2 := by
          by_contra h
          push_neg at h
          have : p % 3 = 0 := by
            omega 
          have h11 : 3 ∣ p := by
            omega 
          have h12 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt h11 (by omega) (by omega)
          have h13 : p.Prime := (hpq).left
          contradiction
        have h8 : q % 3 = 1 ∨ q % 3 = 2 := by
          by_contra h
          push_neg at h
          have : q % 3 = 0 := by
            omega 
          have h14 : 3 ∣ q := by
            omega 
          have h15 : ¬q.Prime := by
            apply Nat.not_prime_of_dvd_of_lt h14 (by omega) (by omega)
          have h16 : q.Prime := (hpq).right
          contradiction
        have hp4 : p ^ 4 % 3 = 1 := by 
          rcases h7 with (h | h) <;> simp [Nat.pow_mod, h]
        have hq4 : q ^ 4 % 3 = 1 := by 
          rcases h8 with (h | h) <;> simp [Nat.pow_mod, h]
        omega
      omega 
  · -- Show 48 is greatest 
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    have h1 : n ∣ (7 ^ 4 - 5 ^ 4 : ℕ) := by 
      apply hn_div 7 5 
      all_goals norm_num
    have h4 : (7 ^ 4 - 5 ^ 4 : ℕ) = 1776 := by 
      norm_num 
    have h2 : n ∣ (11 ^ 4 - 5 ^ 4 : ℕ) := by 
      apply hn_div 11 5 
      all_goals norm_num 
    have h5 : (11 ^ 4 - 5 ^ 4 : ℕ) = 14016 := by 
      norm_num 
    -- Show that n divides 48 
    have h5 : n ∣ 48 := by 
      have h3 : n ∣ 1776 := by 
        rw [h4] at h1 
        exact h1 
      have h4 : n ∣ 14016 := by 
        rw [h5] at h2 
        exact h2 
      exact Nat.dvd_gcd h3 h4 
    have h7 : n ≤ 48 := by 
      exact Nat.le_of_dvd (by linarith) h5 
    linarith