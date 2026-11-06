import Mathlib

theorem number_theory_172986 (n : ℕ) : ¬ 9 ∣ (n^3 + 2) := by
  have h1 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
    omega
  rcases h1 with (h | h | h | h | h | h | h | h | h) <;> ( 
    rw [Nat.dvd_iff_mod_eq_zero] <;> simp [h, Nat.add_mod, Nat.mul_mod, pow_succ]
  )