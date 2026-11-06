import Mathlib

theorem algebra_173682 {x y z : ℝ} (hz : z^2 + 1 ≠ 0)
    (hx : x = (z^4 + z^3 + z^2 + z + 1) / (z^2 + 1))
    (hy : y = (z^3 + z^2 + z + 1) / (z^2 + 1)) :
    (y^2 - 2 * y + 2) * (x + y - y^2) - 1 = 0 := by

  have eq1 : x + y - y^2 = 1 / (z^2 + 1) := by
    rw [hx, hy]
    field_simp [hz]
    ring

  have eq2 : y^2 - 2 * y + 2 = z^2 + 1 := by
    rw [hy]
    field_simp [hz]
    ring

  rw [eq1, eq2]
  field_simp [hz]
  <;> nlinarith