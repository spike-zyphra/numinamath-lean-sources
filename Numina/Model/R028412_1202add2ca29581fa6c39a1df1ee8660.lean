import Mathlib

theorem number_theory_113860 (n : ℕ) (h : (n ^ 2 + 2 * n) % 10 = 4) :
    ((n ^ 2 + 2 * n) / 10) % 10 = 2 := by
  have h1 : n % 10 = 4 := by
    have h2 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, Nat.add_mod, Nat.mul_mod, pow_two] at h <;> omega

  have h24 : (n ^ 2 + 2 * n) % 100 = 24 := by
    have h4 : n % 10 = 4 := h1
    have h10 : n % 100 = 4 ∨ n % 100 = 14 ∨ n % 100 = 24 ∨ n % 100 = 34 ∨ n % 100 = 44 ∨ n % 100 = 54 ∨ n % 100 = 64 ∨ n % 100 = 74 ∨ n % 100 = 84 ∨ n % 100 = 94 := by
      have h14 : n % 10 = 4 := h1
      omega
    rcases h10 with (h10 | h10 | h10 | h10 | h10 | h10 | h10 | h10 | h10 | h10) <;> simp [h10, Nat.add_mod, Nat.mul_mod, pow_two] at *
    all_goals omega

  omega