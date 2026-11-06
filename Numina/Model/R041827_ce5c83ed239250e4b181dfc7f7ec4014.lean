import Mathlib

theorem number_theory_227337 :
    ¬∃ m n : ℕ, ∃ k : ℕ, k^2 = 3^m + 3^n + 1 := by
  rintro ⟨m, n, ⟨k, hk⟩⟩
  have h1 : k^2 % 8 = 0 ∨ k^2 % 8 = 1 ∨ k^2 % 8 = 4 := by
    have h2 : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, Nat.pow_mod, Nat.mul_mod]
  have h2 : (3^m : ℕ) % 8 = 1 ∨ (3^m : ℕ) % 8 = 3 := by
    have h1 : ∀ m : ℕ, (3^m : ℕ) % 8 = 1 ∨ (3^m : ℕ) % 8 = 3 := by
      intro m
      induction m with
      | zero =>
        norm_num
      | succ m ih =>
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        omega
    specialize h1 m
    simpa using h1
  have h3 : (3^n : ℕ) % 8 = 1 ∨ (3^n : ℕ) % 8 = 3 := by
    have h1 : ∀ n : ℕ, (3^n : ℕ) % 8 = 1 ∨ (3^n : ℕ) % 8 = 3 := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        omega
    specialize h1 n
    simpa using h1
  have h4 : (3^m + 3^n + 1) % 8 = 3 ∨ (3^m + 3^n + 1) % 8 = 5 ∨ (3^m + 3^n + 1) % 8 = 7 := by
    omega
  have h5 : k^2 % 8 = (3^m + 3^n + 1) % 8 := by 
    omega
  omega