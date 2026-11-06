import Mathlib

theorem number_theory_247570 (n : ℕ) : 10 ∣ n + 3*n^3 + 7*n^7 + 9*n^9 := by
  have h1 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
    omega
  rcases h1 with (h | h | h | h | h | h | h | h | h | h) <;> (
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, pow_succ, h]
    <;> omega
  )