import Mathlib

theorem algebra_316373 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0)
    (h : x + y + z = 30) (h1 : 9 * x + 15 * y + 8 * z = 45) :
    x = 9 ∧ y = 4 ∧ z = 8 := by
  have h2 : z = 30 - x - y := by linarith
  rw [h2] at h1
  nlinarith