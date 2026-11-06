import Mathlib

theorem number_theory_146462 {n : ℕ} (hn : n > 0) (h : n * n = 10 * k + 2) :
    k = 2 := by
  have h1 : n * n % 10 = 2 := by
    omega
  have h2 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
    omega
  rcases h2 with (h | h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod] at h1 <;> omega