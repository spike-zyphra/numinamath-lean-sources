import Mathlib

theorem number_theory_236458 (n : ℕ) (hn : n > 0) (h : 225 % n = 0) (h' : 105 % n = 0) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by 
  have h1 : n ∣ 225 := by 
    exact Nat.dvd_of_mod_eq_zero h
  have h2 : n ∣ 105 := by 
    exact Nat.dvd_of_mod_eq_zero h'
  have h3 : n ∣ 15 := by 
    exact Nat.dvd_gcd h1 h2
  have h4 : n ≤ 15 := by 
    exact Nat.le_of_dvd (show 0 < 15 by norm_num) h3
  interval_cases n <;> norm_num at h1 h2 h3 h h' ⊢ <;> tauto