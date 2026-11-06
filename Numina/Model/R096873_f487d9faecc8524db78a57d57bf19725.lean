import Mathlib

theorem algebra_16516 (x y : ℝ) (h1 : 3*x-5*y=-11) (h2 : 7*x+2*y=-12) :
    (x,y) = (-2,1) := by
  have hx : x = -2 := by
    linarith [h1, h2]
  have hy : y = 1 := by
    rw [hx] at h2
    linarith
  simp [hx, hy]