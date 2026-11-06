import Mathlib

theorem number_theory_240368 (n : ℕ) (h : ∃ k, n = k^2) :
    12 ∣ n * (n - 1) := by
  rcases h with ⟨k, rfl⟩
  have h1 : (k ^ 2 * (k ^ 2 - 1)) % 3 = 0 := by
    have h2 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · -- k % 3 = 0
      have h3 : k ^ 2 % 3 = 0 := by
        simp [Nat.pow_mod, h2]
      have h4 : (k ^ 2 * (k ^ 2 - 1)) % 3 = 0 := by
        simp [Nat.mul_mod, h3]
      omega
    · -- k % 3 = 1
      have h3 : k ^ 2 % 3 = 1 := by
        simp [Nat.pow_mod, h2]
      have h4 : (k ^ 2 * (k ^ 2 - 1)) % 3 = 0 := by
        simp [Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq, h3]
        <;> omega
      omega
    · -- k % 3 = 2
      have h3 : k ^ 2 % 3 = 1 := by
        simp [Nat.pow_mod, h2]
      have h4 : (k ^ 2 * (k ^ 2 - 1)) % 3 = 0 := by
        simp [Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq, h3]
        <;> omega
      omega
  have h2 : (k ^ 2 * (k ^ 2 - 1)) % 4 = 0 := by
    have h3 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3)
    · -- k % 4 = 0
      have h4 : k ^ 2 % 4 = 0 := by
        simp [Nat.pow_mod, h3]
      have h5 : (k ^ 2 * (k ^ 2 - 1)) % 4 = 0 := by
        simp [Nat.mul_mod, h4]
      exact h5
    · -- k % 4 = 1
      have h4 : k ^ 2 % 4 = 1 := by
        simp [Nat.pow_mod, h3]
      have h6 : (k ^ 2 - 1) % 4 = 0 := by
        omega
      have h5 : (k ^ 2 * (k ^ 2 - 1)) % 4 = 0 := by
        simp [Nat.mul_mod, h4, h6]
      exact h5
    · -- k % 4 = 2
      have h4 : k ^ 2 % 4 = 0 := by
        simp [Nat.pow_mod, h3]
      have h5 : (k ^ 2 * (k ^ 2 - 1)) % 4 = 0 := by
        simp [Nat.mul_mod, h4]
      exact h5
    · -- k % 4 = 3
      have h4 : k ^ 2 % 4 = 1 := by
        simp [Nat.pow_mod, h3]
      have h6 : (k ^ 2 - 1) % 4 = 0 := by
        omega
      have h5 : (k ^ 2 * (k ^ 2 - 1)) % 4 = 0 := by
        simp [Nat.mul_mod, h4, h6]
      exact h5

  omega