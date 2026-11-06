import Mathlib
open Mathlib

theorem algebra_8409 {f : ℝ → ℝ} (h : ∀ x y, y * f x + x * f y = (x + y) * f (x + y)) :
    ∃ c, ∀ x, f x = c := by
  use f 0
  intro x
  have hx1 := h x 0
  have eq1 : x * f 0 = x * f x := by 
    simpa using hx1
  by_cases hx : x = 0
  · 
    rw [hx]
    all_goals linarith
  · 
    have h2 : x ≠ 0 := hx
    have eq2 : f x = f 0 := by
      apply (mul_left_inj' h2).mp
      linarith
    linarith [eq2]