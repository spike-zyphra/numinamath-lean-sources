import Mathlib

theorem number_theory_5009 (n : ℕ) : 6 ∣ n * (n + 1) * (n + 2) := by 
  have h1 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by 
    omega
  rcases h1 with (h | h | h | h | h | h) <;> ( 
    simp [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, h, Nat.add_mod, Nat.mul_mod] <;> omega
  )