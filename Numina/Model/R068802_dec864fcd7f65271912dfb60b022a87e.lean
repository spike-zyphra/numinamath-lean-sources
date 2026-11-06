import Mathlib

theorem number_theory_112448 {a : ℕ} (ha : ∃ m n, m ≠ n ∧ a = m^2 + n^2) :
    ∃ p q, a^2 = p^2 + q^2 := by 
  use a, 0
  simp