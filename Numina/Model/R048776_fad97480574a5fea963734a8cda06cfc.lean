import Mathlib

theorem algebra_256601 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f (x - y) + 4 * x * y) :
    ∃ c, ∀ x, f x = x ^ 2 + c := by 
  use f 0
  intro x
  have eq1 := h (x / 2) (x / 2)
  have eq2 : x / 2 + x / 2 = x := by ring
  have eq3 : x / 2 - x / 2 = (0 : ℝ) := by ring
  have eq4 : 4 * (x / 2) * (x / 2) = x ^ 2 := by ring_nf 
  rw [eq2] at eq1 
  rw [eq3] at eq1 
  linarith [eq1, eq4]