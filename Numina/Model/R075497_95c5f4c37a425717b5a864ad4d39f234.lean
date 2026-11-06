import Mathlib

theorem number_theory_137468 (n k : ℕ) (h₀ : n > 20) (h₁ : k > 1)
    (h₂ : k^2 ∣ n) : ∃ a b c, n = a * b + b * c + c * a := by
  use 0, 1, n
  simp