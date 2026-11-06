import Mathlib

theorem number_theory_302892 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ¬ ∃ a, a^2 = 3^m + 3^n + 1 := by
  rintro ⟨a, ha⟩
  have h1 : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
    have h2 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by omega
    rcases h2 with (h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod]
  have h2 : (3^m) % 8 = 1 ∨ (3^m) % 8 = 3 := by
    have h1 : ∀ k : ℕ, (3 ^ k) % 8 = 1 ∨ (3 ^ k) % 8 = 3 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        simp [Nat.pow_add, Nat.mul_mod] at ih ⊢
        omega
    specialize h1 m
    simpa using h1
  have h3 : (3^n) % 8 = 1 ∨ (3^n) % 8 = 3 := by
    have h1 : ∀ k : ℕ, (3 ^ k) % 8 = 1 ∨ (3 ^ k) % 8 = 3 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        simp [Nat.pow_add, Nat.mul_mod] at ih ⊢
        omega
    specialize h1 n
    simpa using h1
  have h4 : (3^m + 3^n + 1) % 8 = 3 ∨ (3^m + 3^n + 1) % 8 = 5 ∨ (3^m + 3^n + 1) % 8 = 7 := by 
    omega
  have h5 : (a^2) % 8 = (3^m + 3^n + 1) % 8 := by
    omega
  omega