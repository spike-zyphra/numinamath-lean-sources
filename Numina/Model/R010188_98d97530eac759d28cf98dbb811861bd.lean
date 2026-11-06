import Mathlib

open Polynomial

theorem algebra_20637 {a b c d e : ℝ} (h : ∀ x > 0, (5 * x ^ 4 - 8 * x ^ 3 + 2 * x ^ 2 + 4 * x + 7) / (x + 2) ^ 4 =
    a + b / (x + 2) + c / (x + 2) ^ 2 + d / (x + 2) ^ 3 + e / (x + 2) ^ 4) :
    a + b + c + d + e = 18 := by 
  have eqn1 := h 1 (by norm_num)
  have eqn2 := h 2 (by norm_num)
  have eqn3 := h 3 (by norm_num)
  have eqn4 := h 4 (by norm_num)
  have eqn5 := h 5 (by norm_num)
  norm_num at eqn1 eqn2 eqn3 eqn4 eqn5
  linarith