import Mathlib

theorem number_theory_241646 {a b : ℕ} (h : a % 2 ≠ b % 2) :
    ¬ ∃ n, n^2 = (a + 3 * b) * (5 * a + 7 * b) := by 
  rintro ⟨n, hn⟩
  have h1 : (a + 3 * b) * (5 * a + 7 * b) % 8 = 5 := by
    have h4 : (a % 2 = 0 ∧ b % 2 = 1) ∨ (a % 2 = 1 ∧ b % 2 = 0) := by 
      have h2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have h3 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      omega 
    rcases h4 with (h5 | h6)
    · -- case a is even, b is odd 
      have h5' : a % 2 = 0 := h5.1
      have h5'' : b % 2 = 1 := h5.2
      have h5_mod8 : a % 8 = 0 ∨ a % 8 = 2 ∨ a % 8 = 4 ∨ a % 8 = 6 := by 
        omega 
      have h5_mod8' : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by 
        omega 
      rcases h5_mod8 with (h5a | h5a | h5a | h5a) <;> rcases h5_mod8' with (h5b | h5b | h5b | h5b) <;> 
        simp [Nat.mul_mod, Nat.add_mod, h5a, h5b] <;> omega 
    · -- case a is odd, b is even 
      have h6' : a % 2 = 1 := h6.1
      have h6'' : b % 2 = 0 := h6.2
      have h6_mod8 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by 
        omega 
      have h6_mod8' : b % 8 = 0 ∨ b % 8 = 2 ∨ b % 8 = 4 ∨ b % 8 = 6 := by 
        omega 
      rcases h6_mod8 with (h6a | h6a | h6a | h6a) <;> rcases h6_mod8' with (h6b | h6b | h6b | h6b) <;> 
        simp [Nat.mul_mod, Nat.add_mod, h6a, h6b] <;> omega 
  have h2 : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by 
    have h1 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [Nat.pow_mod, h1] 
  have h3 : n ^ 2 % 8 = (a + 3 * b) * (5 * a + 7 * b) % 8 := by 
    omega 
  omega