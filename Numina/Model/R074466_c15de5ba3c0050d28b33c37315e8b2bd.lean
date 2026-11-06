import Mathlib

theorem algebra_10485 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : 2 / x + 3 / y = 0) :
    (y - 3 * x / 2) / (x - 2 * y / 3) = -3 / 2 := by
  have eq1 : 2 * y + 3 * x = 0 := by
    field_simp [hx, hy] at h
    linarith
  have eq2 : y = -3 / 2 * x := by
    linarith
  have eq3 : y - 3 * x / 2 = -3 * x := by
    rw [eq2]
    ring
  have eq4 : x - 2 * y / 3 = 2 * x := by
    rw [eq2]
    ring
  rw [eq3, eq4]
  field_simp [hx]
  <;> ring