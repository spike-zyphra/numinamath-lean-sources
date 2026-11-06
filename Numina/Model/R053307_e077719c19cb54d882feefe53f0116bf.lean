import Mathlib

theorem number_theory_7119 (n : ℕ) (h : n > 0) : 6 ∣ n^3 + 5 * n := by
  have h1 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1) <;> ( 
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, pow_succ, h1, Nat.pow_mod]
    <;> omega
  )