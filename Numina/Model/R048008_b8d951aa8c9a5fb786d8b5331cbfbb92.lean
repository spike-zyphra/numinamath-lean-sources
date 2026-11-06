import Mathlib

theorem number_theory_273007 (n : ℕ) (hn : n > 0) :
    24 ∣ n * (n + 2) * (5 * n - 1) * (5 * n + 1) := by
  have h1 : n * (n + 2) * (5 * n - 1) * (5 * n + 1) % 8 = 0 := by
    have h2 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq] <;> omega

  have h3 : n * (n + 2) * (5 * n - 1) * (5 * n + 1) % 3 = 0 := by
    have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h4 with (h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq] <;> omega

  omega