import Mathlib

theorem number_theory_73069 (n : ℕ) (hn : n > 0) (h1 : ∃ k, k^2 = 2 * n + 1) (h2 : ∃ m, m^2 = 3 * n + 1) :
    40 ∣ n := by
  rcases h1 with ⟨k, hk⟩
  rcases h2 with ⟨m, hm⟩
  have h3 : n > 0 := hn
  have h4 : k^2 = 2 * n + 1 := by
    linarith
  have h5 : m^2 = 3 * n + 1 := by
    linarith
  have h6 : n % 8 = 0 := by
    by_contra h
    push_neg at h
    have h8k : k^2 % 8 = 0 ∨ k^2 % 8 = 1 ∨ k^2 % 8 = 4 := by 
      have h1 : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
    have h8m : m^2 % 8 = 0 ∨ m^2 % 8 = 1 ∨ m^2 % 8 = 4 := by 
      have h1 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by 
        omega 
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
    omega 
  have h7 : n % 5 = 0 := by
    by_contra h
    push_neg at h
    have h5k : k^2 % 5 = 0 ∨ k^2 % 5 = 1 ∨ k^2 % 5 = 4 := by 
      have h1 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by 
        omega 
      rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
      simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
    have h5m : m^2 % 5 = 0 ∨ m^2 % 5 = 1 ∨ m^2 % 5 = 4 := by 
      have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by 
        omega 
      rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
      simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
    omega
  omega