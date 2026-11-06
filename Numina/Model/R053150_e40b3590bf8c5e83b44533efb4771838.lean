import Mathlib

theorem algebra_93913 {w x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : w / x = 4 / 3) (h2 : y / z = 3 / 2) (h3 : z / x = 1 / 6) :
    w / y = 16 / 3 := by
  have eq1 : 3 * w = 4 * x := by
    field_simp [hx] at h1
    linarith
  have eq2 : 2 * y = 3 * z := by
    field_simp [hz] at h2
    linarith
  have eq3 : 6 * z = x := by
    field_simp [hx] at h3
    linarith
  have eq4 : w = 8 * z := by
    linarith [eq1, eq3]
  have eq5 : y = (3 / 2) * z := by
    linarith [eq2]
  -- Now, compute $\frac{w}{y}$
  have : w / y = 16 / 3 := by
    rw [eq4, eq5]
    field_simp [hz]
    <;> linarith
  exact this