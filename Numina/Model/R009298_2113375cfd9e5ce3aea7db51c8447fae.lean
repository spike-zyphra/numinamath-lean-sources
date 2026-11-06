import Mathlib

theorem algebra_10410 {g h : ℝ} (h₀ : ∀ d : ℝ, (7 * d ^ 2 - 3 * d + g) * (3 * d ^ 2 + h * d - 8) = 21 * d ^ 4 - 44 * d ^ 3 - 35 * d ^ 2 + 14 * d - 16) :
    g + h = -3 := by 
  have eqn1 := h₀ 0
  have eqn2 := h₀ 1
  have eqn3 := h₀ 2
  have eqn4 := h₀ 3
  have eqn5 := h₀ (-1)
  norm_num at eqn1 eqn2 eqn3 eqn4 eqn5
  linarith