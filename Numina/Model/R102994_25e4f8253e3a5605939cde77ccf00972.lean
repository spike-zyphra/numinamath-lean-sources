import Mathlib

theorem number_theory_292811 (n : ℕ) :
    ¬∃ k : ℕ, n * (n + 1) = 25 * k + 1 := by 
  rintro ⟨k, hk⟩
  have eq1 : n * (n + 1) % 25 = 1 := by 
    omega
  have : n % 25 = 0 ∨ n % 25 = 1 ∨ n % 25 = 2 ∨ n % 25 = 3 ∨ n % 25 = 4 ∨ n % 25 = 5 ∨ n % 25 = 6 ∨ n % 25 = 7 ∨ n % 25 = 8 ∨ n % 25 = 9 ∨ n % 25 = 10 ∨ n % 25 = 11 ∨ n % 25 = 12 ∨ n % 25 = 13 ∨ n % 25 = 14 ∨ n % 25 = 15 ∨ n % 25 = 16 ∨ n % 25 = 17 ∨ n % 25 = 18 ∨ n % 25 = 19 ∨ n % 25 = 20 ∨ n % 25 = 21 ∨ n % 25 = 22 ∨ n % 25 = 23 ∨ n % 25 = 24 := by
    omega
  rcases this with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod] at eq1 <;> omega