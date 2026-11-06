import Mathlib

theorem reflected_hyperbola_equation (x₀ y₀ : ℝ) (h₀ : x₀ * y₀ = 1) :
    let x := (-3 * x₀ + 4 * y₀) / 5
    let y := (4 * x₀ + 3 * y₀) / 5
    12 * y ^ 2 + 7 * x * y - 12 * x ^ 2 = 25 :=
by
  intro x y
  -- Substitute the expressions for $x$ and $y$ in terms of $x₀$ and $y₀$.
  -- $x = \frac{-3x₀ + 4y₀}{5}$ and $y = \frac{4x₀ + 3y₀}{5}$.
  have h₁ : 12 * y ^ 2 + 7 * x * y - 12 * x ^ 2 = 25 := by 
    simp only [x, y]
    nlinarith [h₀, sq_nonneg (x₀ - y₀), sq_nonneg (x₀ + y₀), sq_nonneg (2 * x₀ - y₀), sq_nonneg (2 * y₀ - x₀)]
  exact h₁