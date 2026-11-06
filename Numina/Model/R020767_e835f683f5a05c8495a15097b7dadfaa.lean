import Mathlib

theorem algebra_311062 {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x + 1 / y = 1) (hyz : y + 1 / z = 1) :
    x * y * z = -1 := by
  have eq1 : x * y + 1 = y := by
    have h1 : x + 1 / y = 1 := hxy
    field_simp [hy] at h1 ⊢
    linarith
  have eq2 : y * z + 1 = z := by
    have h2 : y + 1 / z = 1 := hyz
    field_simp [hz] at h2 ⊢
    linarith
  have eq3 : x * y = y - 1 := by
    linarith
  have eq4 : y * z = z - 1 := by
    linarith
  calc
    x * y * z = (x * y) * z := by ring
    _ = (y - 1) * z := by rw [eq3]
    _ = (y * z) - z := by ring
    _ = (z - 1) - z := by rw [eq4]
    _ = -1 := by ring