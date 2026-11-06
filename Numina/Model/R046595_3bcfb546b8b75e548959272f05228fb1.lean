import Mathlib

theorem algebra_13914 (a b : ℕ → ℝ)
    (h₀ : a 0 = 2) (h₁ : b 0 = 3)
    (h₂ : ∀ n, a (n + 1) = (a n)^2 / b n)
    (h₃ : ∀ n, b (n + 1) = (b n)^2 / a n) :
    ∃ m n, b 8 = 3^m / 2^n ∧ (m, n) = (3281, 3280) := by
  use 3281, 3280
  constructor
  · -- Calculate b 8 using the recurrence relations.
    norm_num [h₀, h₁, h₂, h₃]
  · -- Show that (3281, 3280) = (3281, 3280)
    rfl