import Mathlib

theorem algebra_15765 {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (h₀ : x + 1 / y = 1) (h₁ : y + 1 / z = 1) :
    x * y * z = -1 := by
  have eq1 : x * y = y - 1 := by
    field_simp [hy] at h₀
    linarith
  have eq2 : y * z = z - 1 := by
    field_simp [hz] at h₁
    linarith
  calc
    x * y * z = (x * y) * z := by ring
    _ = (y - 1) * z := by rw [eq1]
    _ = (y * z) - z := by ring
    _ = (z - 1) - z := by rw [eq2]
    _ = -1 := by ring