import Mathlib

theorem algebra_228898 {f : ℝ → ℝ} (h : ∀ x, 4 * f (3 - x) - f x = 3 * x ^ 2 - 4 * x - 3) :
    ∃ x y, x ≠ y ∧ f x = 8 ∧ f y = 8 ∧ x * y = -5 := by

  have hfx : ∀ x, f x = x^2 - 4*x + 3 := by
    intro x
    have eq1 := h x
    have eq2 := h (3 - x)
    simp [show 3 - (3 - x) = x by ring] at eq2
    linarith

  have hx1 : f 5 = 8 := by
    rw [hfx]
    norm_num

  have hx2 : f (-1) = 8 := by
    rw [hfx]
    norm_num

  use 5, -1
  constructor
  · -- distinct
    norm_num
  constructor
  · exact hx1
  constructor
  · exact hx2
  · -- product is -5
    norm_num