import Mathlib

theorem number_theory_104985 (a b c d e : ℕ) (h₀ : a * b * c * d * e = 15 * (a - 3) * (b - 3) * (c - 3) * (d - 3) * (e - 3)) :
    a * b * c * d * e = 15 * (a - 3) * (b - 3) * (c - 3) * (d - 3) * (e - 3) := by
  exact h₀