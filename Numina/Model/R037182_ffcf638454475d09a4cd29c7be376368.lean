import Mathlib

theorem number_theory_179698 (m n : ℕ) (hnm : Odd n) :
    ¬ ∃ k, k^2 = m * (m + 2) + n * (n + 2) := by 
  rintro ⟨k, hk⟩
  have h1 : n % 2 = 1 := by 
    rcases hnm with ⟨t, ht⟩
    omega
  have h2 : k^2 % 8 = 0 ∨ k^2 % 8 = 1 ∨ k^2 % 8 = 4 := by
    have h1 : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by 
      omega
    rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod]
  have h3 : (m * (m + 2) + n * (n + 2)) % 8 = 2 ∨ (m * (m + 2) + n * (n + 2)) % 8 = 3 ∨ (m * (m + 2) + n * (n + 2)) % 8 = 6 ∨ (m * (m + 2) + n * (n + 2)) % 8 = 7 := by
    have h4 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
      have h1 : n % 2 = 1 := by 
        omega
      omega
    have h5 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by 
      omega
    rcases h4 with (h4 | h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;> simp [Nat.add_mod, Nat.mul_mod, h4, h5] at *
  have h4 : k^2 % 8 = (m * (m + 2) + n * (n + 2)) % 8 := by
    omega
  omega