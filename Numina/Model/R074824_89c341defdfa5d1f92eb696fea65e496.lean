import Mathlib

theorem number_theory_150981 (n : ℕ) : 2 ∣ n^2 + n := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by
    omega
  rcases h with (h | h)
  · 
    have h1 : n % 2 = 0 := h
    have h2 : (n ^ 2 + n) % 2 = 0 := by
      have hn1 : n % 2 = 0 := h1
      have h_nsq : (n ^ 2) % 2 = 0 := by
        simp [Nat.pow_mod, hn1]
      have h_n : n % 2 = 0 := hn1
      omega 
    exact Nat.dvd_of_mod_eq_zero h2 
  · 
    have h1 : n % 2 = 1 := h
    have h2 : (n ^ 2 + n) % 2 = 0 := by
      have hn1 : n % 2 = 1 := h1
      have h_nsq : (n ^ 2) % 2 = 1 := by
        simp [Nat.pow_mod, hn1]
      have h_n : n % 2 = 1 := hn1
      omega 
    exact Nat.dvd_of_mod_eq_zero h2