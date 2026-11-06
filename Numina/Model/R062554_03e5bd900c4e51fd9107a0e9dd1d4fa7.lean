import Mathlib

def f (x y a b : ℝ) := (x * a + y * b, x * b + y * a)

theorem algebra_236874 {a b : ℝ} (h : ∀ x y, f x y a b = (x, y)) :
    a = 1 ∧ b = 0 := by
  have eq1 := h 1 0
  simp [f] at eq1
  have eq2 := h 0 1
  simp [f] at eq2
  constructor
  · linarith [eq1.1, eq2.2]
  · linarith [eq1.2, eq2.1]