import Mathlib

theorem algebra_172509 {x y z : ℝ} (h : x + y + z = 0) :
    (x^2 + y^2 + z^2)/2 * (x^5 + y^5 + z^5)/5 = (x^7 + y^7 + z^7)/7 := by
  have h1 : z = -(x + y) := by linarith
  rw [h1]
  ring_nf