import Mathlib

theorem algebra_145027 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h : x + y = z) :
    (z / x + y / z - x / y + x / z + z / y - y / x = 3) := by

  have h1 : z = x + y := by
    linarith
  rw [show z = x + y by linarith [h]]
  have h2 : x + y ≠ 0 := by
    intro h'
    have : z = 0 := by
      linarith [h']
    contradiction

  field_simp [show x ≠ 0 by exact hx, show y ≠ 0 by exact hy, show x + y ≠ 0 by exact h2, hx, hy]
  <;> nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_pos_of_ne_zero (show x + y ≠ 0 by exact h2)]