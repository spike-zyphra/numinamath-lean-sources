import Mathlib

theorem algebra_10870 {A B : ℝ} (h : ∀ x, x ≠ 2 → x ≠ 5 →  (B * x - 11) / (x ^ 2 - 7 * x + 10) = A / (x - 2) + 3 / (x - 5)) :
    A + B = 5 := by
  have eqn1 := h 1 (by norm_num) (by norm_num)
  have eqn2 := h 3 (by norm_num) (by norm_num)
  norm_num at eqn1 eqn2
  linarith