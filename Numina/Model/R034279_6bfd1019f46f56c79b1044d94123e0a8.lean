import Mathlib

theorem number_theory_194896 (n : ℕ) : 720 ∣ (n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5)) := by
  have h1 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) % 16 = 0 := by
    have h2 : n % 16 = 0 ∨ n % 16 = 1 ∨ n % 16 = 2 ∨ n % 16 = 3 ∨ n % 16 = 4 ∨ n % 16 = 5 ∨ n % 16 = 6 ∨ n % 16 = 7 ∨ n % 16 = 8 ∨ n % 16 = 9 ∨ n % 16 = 10 ∨ n % 16 = 11 ∨ n % 16 = 12 ∨ n % 16 = 13 ∨ n % 16 = 14 ∨ n % 16 = 15 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod, Nat.mul_mod, Nat.add_mod]
  have h2 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) % 9 = 0 := by
    have h3 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
      omega
    rcases h3 with (h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod, Nat.mul_mod, Nat.add_mod]
  have h3 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) % 5 = 0 := by
    have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h4 with (h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod, Nat.mul_mod, Nat.add_mod]
  omega