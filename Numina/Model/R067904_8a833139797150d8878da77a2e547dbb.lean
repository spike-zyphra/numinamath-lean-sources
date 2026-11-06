import Mathlib

def T_type (n : ℕ) := n > 0 ∧ n % 3 = 1

theorem number_theory_299633 (n : ℕ) :
    ¬T_type (3 * n - 1) := by
  intro h
  have h1 : (3 * n - 1) > 0 := h.1
  have h2 : (3 * n - 1) % 3 = 1 := h.2
  have h3 : (3 * n) % 3 = 0 := by
    simp [Nat.mul_mod]
  omega