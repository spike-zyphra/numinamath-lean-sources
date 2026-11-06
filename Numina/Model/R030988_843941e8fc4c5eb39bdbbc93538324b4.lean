import Mathlib

theorem number_theory_226525 (n : ℕ) :
  ¬ ∃ m, n^2 + 101010 = m^2
:= by
  rintro ⟨m, hm⟩
  have h1 : (m : ℕ) ^ 2 % 4 = 0 ∨ (m : ℕ) ^ 2 % 4 = 1 := by
    have h2 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [Nat.pow_mod, Nat.mul_mod, h2]
  have h2 : (n : ℕ) ^ 2 % 4 = 0 ∨ (n : ℕ) ^ 2 % 4 = 1 := by
    have h2 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [Nat.pow_mod, Nat.mul_mod, h2]
  have h5 : (101010 : ℕ) % 4 = 2 := by norm_num
  have h6 : (m ^ 2 : ℕ) % 4 = (n ^ 2 + 101010) % 4 := by
    omega
  omega