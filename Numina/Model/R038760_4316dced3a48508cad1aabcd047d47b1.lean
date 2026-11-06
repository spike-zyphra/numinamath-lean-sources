import Mathlib

theorem number_theory_65043 (n : ℕ) (hn : n > 0) (h : ∃ k, n^5 + n^3 + 2*n^2 + 2*n + 2 = k^3) :
    ¬∃ m, m^3 = 2*n^2 + n + 2 := by
  intro h1
  rcases h1 with ⟨m, hm⟩
  rcases h with ⟨k, hk⟩
  have h4 : m^3 % 9 = 0 ∨ m^3 % 9 = 1 ∨ m^3 % 9 = 8 := by
    have h1 : m % 9 = 0 ∨ m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 3 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 7 ∨ m % 9 = 8 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [h1, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
  have h6 : m^3 % 9 = (2 * n^2 + n + 2) % 9 := by
    omega
  have h9 : (2 * n^2 + n + 2) % 9 = 0 ∨ (2 * n^2 + n + 2) % 9 = 1 ∨ (2 * n^2 + n + 2) % 9 = 8 := by
    omega
  have h5 : k^3 % 9 = 0 ∨ k^3 % 9 = 1 ∨ k^3 % 9 = 8 := by
    have h1 : k % 9 = 0 ∨ k % 9 = 1 ∨ k % 9 = 2 ∨ k % 9 = 3 ∨ k % 9 = 4 ∨ k % 9 = 5 ∨ k % 9 = 6 ∨ k % 9 = 7 ∨ k % 9 = 8 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [h1, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
  have h7 : k^3 % 9 = (n^5 + n^3 + 2 * n^2 + 2 * n + 2) % 9 := by
    omega
  have h10 : (n^5 + n^3 + 2 * n^2 + 2 * n + 2) % 9 = 0 ∨ (n^5 + n^3 + 2 * n^2 + 2 * n + 2) % 9 = 1 ∨ (n^5 + n^3 + 2 * n^2 + 2 * n + 2) % 9 = 8 := by
    omega
  have h100 : (n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8) := by
    omega
  rcases h100 with (h100 | h100 | h100 | h100 | h100 | h100 | h100 | h100 | h100) <;> 
    simp [h100, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at h10 h9
    <;> try { 
      omega
    }