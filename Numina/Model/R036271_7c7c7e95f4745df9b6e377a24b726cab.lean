import Mathlib

theorem algebra_21706 {x y : ℝ} (h : 5 * x - 9 * y = 42) (h' : x = -y) :
    (x, y) = (3, -3) := by
  have eq1 : 5 * x - 9 * y = 42 := h
  rw [show x = -y by linarith [h']] at eq1
  have hy : y = -3 := by
    linarith
  have hx : x = 3 := by
    linarith [h', hy]
  simp [Prod.ext_iff, hx, hy]