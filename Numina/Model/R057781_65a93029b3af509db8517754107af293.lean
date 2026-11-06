import Mathlib

theorem number_theory_97957 :
    IsGreatest {k | ∀ m n : ℕ, Odd m → Odd n → n < m → k ∣ m ^ 2 - n ^ 2} 8 := by 
  constructor
  · -- Show 8 is in the set.
    intro m n h_odd_m h_odd_n h_lt
    have h1 : m % 2 = 1 := by
      rcases h_odd_m with ⟨k, hk⟩
      omega
    have h2 : n % 2 = 1 := by
      rcases h_odd_n with ⟨k, hk⟩
      omega
    have h3 : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by 
      have h_odd : m % 2 = 1 := by 
        have h_odd_m' : Odd m := h_odd_m
        rcases h_odd_m with ⟨k, hk⟩
        omega
      omega
    have h4 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by 
      have h_odd : n % 2 = 1 := by 
        have h_odd_n' : Odd n := h_odd_n
        rcases h_odd_n with ⟨k, hk⟩
        omega
      omega
    have h5 : m ^ 2 % 8 = 1 := by
      rcases h3 with (h | h | h | h) <;> norm_num [Nat.pow_mod, h] at *
    have h6 : n ^ 2 % 8 = 1 := by
      rcases h4 with (h | h | h | h) <;> norm_num [Nat.pow_mod, h] at *
    have h7 : (m ^ 2 - n ^ 2) % 8 = 0 := by 
      omega
    exact Nat.dvd_of_mod_eq_zero h7
  · -- Show no integer greater than 8 is in the set.
    intro k h
    have h1 := h 3 1 (by decide) (by decide) (by norm_num)
    norm_num at h1
    have h2 := h 5 3 (by decide) (by decide) (by norm_num)
    norm_num at h2
    have h3 := h 5 1 (by decide) (by decide) (by norm_num)
    norm_num at h3
    have h4 := h 7 5 (by decide) (by decide) (by norm_num)
    norm_num at h4
    have h6 : k ∣ 8 := by
      exact Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    have h7 : k ≤ 8 := by 
      exact Nat.le_of_dvd (by norm_num) h6
    linarith