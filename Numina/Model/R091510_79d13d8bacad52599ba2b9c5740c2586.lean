import Mathlib

open Polynomial

theorem algebra_5926 {a b c d : ℝ} (h : ∀ (x : ℝ), (a * x^3 + b * x^2 + c * x + d) = (3 * x + 1) * (x^2 + 5 * x + 3) + (x - 2)) :
    a + b + c + d = 35 := by
  have eq1 := h 1
  norm_num at eq1
  linarith