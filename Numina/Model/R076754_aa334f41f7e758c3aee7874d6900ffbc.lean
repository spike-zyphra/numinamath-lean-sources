import Mathlib

theorem algebra_184735 (f : ℝ → ℝ) (x₀ : ℝ) (h : ∀ x, f x = 2 * x ^ 2 - 3 * x + 4) :
    f (x₀ - 1) = f (x₀ + 1) - 8 * x₀ + 6 := by 
  have eq1 : f (x₀ - 1) = 2 * (x₀ - 1) ^ 2 - 3 * (x₀ - 1) + 4 := h (x₀ - 1)
  have eq2 : f (x₀ + 1) = 2 * (x₀ + 1) ^ 2 - 3 * (x₀ + 1) + 4 := h (x₀ + 1)
  rw [eq1, eq2]
  ring_nf