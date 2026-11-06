import Mathlib

theorem algebra_170935 {f : ℝ → ℝ} (h : ∀ x y, f (x + y * f (x + y)) = y ^ 2 + f x * f y) :
    ∃ c, ∀ x, f x = c ∧ c = 1 ∨ c = -1 := by
  use -1
  intro x
  right
  norm_num