import Mathlib

theorem number_theory_233308 (n : ℕ) : 6 ∣ (n + 20) * (n + 201) * (n + 2020) := by
  have h1 : (n + 20) * (n + 201) * (n + 2020) % 6 = 0 := by
    have h2 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
      omega
    rcases h2 with (h | h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod]
  omega