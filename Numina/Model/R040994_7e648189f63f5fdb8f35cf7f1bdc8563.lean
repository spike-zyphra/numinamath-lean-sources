import Mathlib
open Mathlib

lemma algebra_1207 (f : ℝ → ℝ) (a b c : ℝ) (h1 : ∀ x, f (x + 3) = 3 * x^2 + 7*x + 4) (h2 : ∀ x, f x = a * x^2 + b * x + c) : a + b + c = 2 := by
  have eq5 := h1 (-2)
  norm_num at eq5 
  have eq6 := h2 1
  norm_num at eq6
  linarith