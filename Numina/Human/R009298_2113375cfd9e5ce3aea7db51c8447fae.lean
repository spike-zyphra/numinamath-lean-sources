import Mathlib

/- The product of $7d^2-3d+g$ and $3d^2+hd-8$ is $21d^4-44d^3-35d^2+14d-16$. What is $g+h$? -/
theorem algebra_10410 {g h : ℝ} (h₀ : ∀ d : ℝ, (7 * d ^ 2 - 3 * d + g) * (3 * d ^ 2 + h * d - 8) = 21 * d ^ 4 - 44 * d ^ 3 - 35 * d ^ 2 + 14 * d - 16) :
    g + h = -3 := by 
  have h₁ := h₀ 1
  have h₂ := h₀ (-1)
  have h₃ := h₀ 0
  linarith