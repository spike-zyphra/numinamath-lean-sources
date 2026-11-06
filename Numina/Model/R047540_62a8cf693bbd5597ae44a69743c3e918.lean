import Mathlib

theorem number_theory_237887 (n : ℕ) (h₀ : n = 10^99 - 1) :
    ∃ m, IsSquare (n * 10^100 + m) := by
  use (10^200 - 10^199 + 10^100)
  rw [h₀]
  native_decide