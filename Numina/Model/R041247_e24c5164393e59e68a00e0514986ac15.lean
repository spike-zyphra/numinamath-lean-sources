import Mathlib

theorem number_theory_192047 (n : ℕ) : 120 ∣ n^7 - n^3 := by
  have h1 : n ^ 7 % 8 = n ^ 3 % 8 := by
    have h2 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h2 : n ^ 7 % 3 = n ^ 3 % 3 := by
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h3 with (h3 | h3 | h3) <;> simp [Nat.pow_mod, h3]
  have h3 : n ^ 7 % 5 = n ^ 3 % 5 := by
    have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4) <;> simp [Nat.pow_mod, h4]
  omega