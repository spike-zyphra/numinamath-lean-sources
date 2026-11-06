import Mathlib

theorem number_theory_233410 (n : ℕ) (h : n * (n + 2) ≡ 4 [MOD 10]) :
    (n * (n + 2)) % 100 = 24 ∨ (n * (n + 2)) % 100 = 46 ∨ (n * (n + 2)) % 100 = 68 := by
  have h1 : n % 10 = 4 := by
    simp [Nat.ModEq] at h
    have h1 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
    simp [h1, Nat.add_mod, Nat.mul_mod] at h ⊢
    <;> omega
  have h8 : (n * (n + 2)) % 100 = 24 := by
    have h9 : n % 10 = 4 := h1
    have : n % 100 = 4 ∨ n % 100 = 14 ∨ n % 100 = 24 ∨ n % 100 = 34 ∨ n % 100 = 44 ∨ n % 100 = 54 ∨ n % 100 = 64 ∨ n % 100 = 74 ∨ n % 100 = 84 ∨ n % 100 = 94 := by
        omega
    rcases this with (h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9) <;> 
      simp [h9, Nat.add_mod, Nat.mul_mod]
      <;> omega
  left
  exact h8