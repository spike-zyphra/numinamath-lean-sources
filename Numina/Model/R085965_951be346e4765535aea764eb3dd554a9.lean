import Mathlib

theorem number_theory_252662 (n : ℕ) : 7 ∣ n^7 - n := by
  have h1 : n^7 % 7 = n % 7 := by
    have h2 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by 
      omega
    rcases h2 with (h | h | h | h | h | h | h) <;> simp [h, pow_succ, Nat.mul_mod]
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h1)