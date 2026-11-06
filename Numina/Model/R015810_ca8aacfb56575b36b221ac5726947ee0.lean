import Mathlib

theorem number_theory_23430 (n : ℕ) (hn : n % 7 = 3) : (2 * n + 1) % 7 = 0 := by
  have h1 : n % 7 = 3 := hn
  have h4 : (2 * n + 1) % 7 = 0 := by
    have h5 : n % 7 = 3 := h1
    simp [Nat.add_mod, Nat.mul_mod, h5]
    <;> omega
  exact h4