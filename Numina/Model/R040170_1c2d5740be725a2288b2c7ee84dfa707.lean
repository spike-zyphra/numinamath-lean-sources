import Mathlib

theorem negated_number_theory_56441 {b c : ℕ} (h₀ : b ∣ c + 1) :
    ∃ x y z, x + y = b * z ∧ x * y = c * z := by
  use 0, 0, 0
  constructor
  · -- Show that 0 + 0 = b * 0
    simp
  · -- Show that 0 * 0 = c * 0
    simp