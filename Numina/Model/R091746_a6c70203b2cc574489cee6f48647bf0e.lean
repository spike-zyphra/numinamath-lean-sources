import Mathlib

theorem number_theory_242208 (x : ℕ) : ¬ 5 ∣ x → 5 ∣ (x ^ 4 - 1) := by
  intro h
  have h1 : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1)
  · -- Case x % 5 = 1
    have h2 : x ^ 4 % 5 = 1 := by
      have h3 : x % 5 = 1 := h1
      norm_num [Nat.pow_mod, h3]
    omega
  · -- Case x % 5 = 2
    have h2 : x ^ 4 % 5 = 1 := by
      have h3 : x % 5 = 2 := h1
      norm_num [Nat.pow_mod, h3]
    omega
  · -- Case x % 5 = 3
    have h2 : x ^ 4 % 5 = 1 := by
      have h3 : x % 5 = 3 := h1
      norm_num [Nat.pow_mod, h3]
    omega
  · -- Case x % 5 = 4
    have h2 : x ^ 4 % 5 = 1 := by
      have h3 : x % 5 = 4 := h1
      norm_num [Nat.pow_mod, h3]
    omega