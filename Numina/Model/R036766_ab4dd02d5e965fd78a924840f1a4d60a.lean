import Mathlib

theorem number_theory_184785 : ¬∃ n m, n ≠ m ∧ (n^2 + 4 * n) - (m^2 + 4 * m) = 1998 := by 
  rintro ⟨n, m, hneq, heq⟩
  have h1 : (n : ℕ) ^ 2 + 4 * (n : ℕ) ≥ (m : ℕ) ^ 2 + 4 * (m : ℕ) := by
    omega
  have h2 : (n : ℕ) ^ 2 + 4 * (n : ℕ) = (m : ℕ) ^ 2 + 4 * (m : ℕ) + 1998 := by
    omega
  have eq1 : (n^2 + 4 * n) % 8 = (m^2 + 4 * m + 1998) % 8 := by
    omega
  have h5 : (n : ℕ) % 8 = 0 ∨ (n : ℕ) % 8 = 1 ∨ (n : ℕ) % 8 = 2 ∨ (n : ℕ) % 8 = 3 ∨ (n : ℕ) % 8 = 4 ∨ (n : ℕ) % 8 = 5 ∨ (n : ℕ) % 8 = 6 ∨ (n : ℕ) % 8 = 7 := by 
    omega
  have h6 : (m : ℕ) % 8 = 0 ∨ (m : ℕ) % 8 = 1 ∨ (m : ℕ) % 8 = 2 ∨ (m : ℕ) % 8 = 3 ∨ (m : ℕ) % 8 = 4 ∨ (m : ℕ) % 8 = 5 ∨ (m : ℕ) % 8 = 6 ∨ (m : ℕ) % 8 = 7 := by 
    omega
  rcases h5 with (h | h | h | h | h | h | h | h) <;> rcases h6 with (h' | h' | h' | h' | h' | h' | h' | h') <;> norm_num [h, h', Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at eq1 <;> omega