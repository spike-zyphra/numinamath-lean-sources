import Mathlib

theorem algebra_294315 {x y z : ℝ} (h : x ≠ 0) (h1 : y ≠ 0) (h2 : z ≠ 0)
    (h3 : x / 3 = y / -4) (h4 : y / -4 = z / 7) :
    (3 * x + y + z) / y = -3 := by
  have h5 : x / 3 = z / 7 := by
    linarith
  have eq1 : y = -4 / 3 * x := by
    field_simp at h3
    linarith
  have eq2 : z = 7 / 3 * x := by
    field_simp at h5
    linarith
  have eq3 : 3 * x + y + z = 4 * x := by
    rw [eq1, eq2]
    linarith
  have eq4 : 3 * x + y + z = -3 * y := by
    linarith [eq3, eq1]
  have h7 : y ≠ 0 := h1
  field_simp [h7]
  linarith [eq4]