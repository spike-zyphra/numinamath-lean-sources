import Mathlib

theorem algebra_10274 {A B : ℝ} (h : ∀ x, x ≠ 5 → A / (x - 5) + B * (x + 1) = (-3 * x ^ 2 + 12 * x + 22) / (x - 5)) :
    A + B = 4 := by
  have eqn1 := h 6 (by norm_num)
  have eqn2 := h 4 (by norm_num)
  have eqn3 := h 7 (by norm_num)
  norm_num at eqn1 eqn2 eqn3
  linarith