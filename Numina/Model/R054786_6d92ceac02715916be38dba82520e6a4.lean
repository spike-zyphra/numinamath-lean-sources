import Mathlib

theorem number_theory_253294 (n : ℕ) (h₀ : n > 0) :
    (n * (n + 1) * (n + 2) * (n + 3) * (n + 4)) % 10 = 0 := by 
  have h1 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
    omega 
  rcases h1 with (h | h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod]
  <;> omega