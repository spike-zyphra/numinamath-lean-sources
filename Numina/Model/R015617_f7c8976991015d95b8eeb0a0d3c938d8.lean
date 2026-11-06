import Mathlib

theorem number_theory_228277 {n : ℕ} (h : ∃ k, n = k^2) :
    12 ∣ n * (n - 1) := by
  rcases h with ⟨k, rfl⟩
  have h1 : (k^2 * (k^2 - 1)) % 3 = 0 := by 
    have h2 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h2 with (h2 | h2 | h2)
    · -- Case k % 3 = 0
      have h3 : k ^ 2 % 3 = 0 := by 
        simp [Nat.pow_mod, h2]
      have h5 : k ^ 2 * (k^2 - 1) % 3 = 0 := by 
        simp [Nat.mul_mod, h3, Nat.sub_mod_eq_zero_of_mod_eq]
      exact h5
    · -- Case k % 3 = 1
      have h3 : k ^ 2 % 3 = 1 := by 
        simp [Nat.pow_mod, h2]
      have h4 : (k ^ 2 - 1) % 3 = 0 := by 
        omega
      have h5 : k ^ 2 * (k^2 - 1) % 3 = 0 := by 
        simp [Nat.mul_mod, h4]
      exact h5
    · -- Case k % 3 = 2
      have h3 : k ^ 2 % 3 = 1 := by 
        simp [Nat.pow_mod, h2]
      have h4 : (k ^ 2 - 1) % 3 = 0 := by 
        omega
      have h5 : k ^ 2 * (k^2 - 1) % 3 = 0 := by 
        simp [Nat.mul_mod, h4]
      exact h5
  have h2 : (k^2 * (k^2 - 1)) % 4 = 0 := by 
    have h2 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases h2 with (h2 | h2 | h2 | h2)
    · -- Case k % 4 = 0
      have h3 : k ^ 2 % 4 = 0 := by
        simp [Nat.pow_mod, h2]
      have h6 : k^2 * (k^2 - 1) % 4 = 0 := by
        have : k ^ 2 % 4 = 0 := h3
        have eq1 : (k ^ 2 * (k^2 - 1)) % 4 = 0 := by
          simp [Nat.mul_mod, this, Nat.sub_mod_eq_zero_of_mod_eq]
        exact_mod_cast eq1
      exact_mod_cast h6
    · -- Case k % 4 = 1
      have h3 : k ^ 2 % 4 = 1 := by
        simp [Nat.pow_mod, h2]
      have h4 : (k ^ 2 - 1) % 4 = 0 := by
        have h3' : k ^ 2 % 4 = 1 := h3
        have : k ^ 2 % 4 = 1 := h3'
        omega
      have h6 : k^2 * (k^2 - 1) % 4 = 0 := by
        have h4' : (k ^ 2 - 1) % 4 = 0 := h4
        simp [Nat.mul_mod, h4']
      exact_mod_cast h6
    · -- Case k % 4 = 2
      have h3 : k ^ 2 % 4 = 0 := by
        simp [Nat.pow_mod, h2]
      have h6 : k^2 * (k^2 - 1) % 4 = 0 := by
        have : k ^ 2 % 4 = 0 := h3
        simp [Nat.mul_mod, this, Nat.sub_mod_eq_zero_of_mod_eq]
      exact_mod_cast h6
    · -- Case k % 4 = 3
      have h3 : k ^ 2 % 4 = 1 := by
        simp [Nat.pow_mod, h2]
      have h4 : (k ^ 2 - 1) % 4 = 0 := by
        have h3' : k ^ 2 % 4 = 1 := h3
        have : k ^ 2 % 4 = 1 := h3'
        omega
      have h6 : k^2 * (k^2 - 1) % 4 = 0 := by
        have h4' : (k ^ 2 - 1) % 4 = 0 := h4
        simp [Nat.mul_mod, h4']
      exact_mod_cast h6
  omega