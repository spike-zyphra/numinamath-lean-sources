import Mathlib

theorem algebra_135478 (x y z : ℝ) (h : (x - 7) / 3 = (y - 3) / 1) (h' : (y - 3) / 1 = (z + 1) / -2)
    (h'' : 2 * x + y + 7 * z - 3 = 0) :
    (x, y, z) = (10, 4, -3) := by
  have eq1 : x - 7 = 3 * (y - 3) := by
    field_simp at h
    linarith
  have eq2 : -2 * (y - 3) = (z + 1) := by
    field_simp at h'
    linarith
  have eq3 : z = -2 * y + 5 := by
    linarith [eq2]
  have eqy : y = 4 := by
    rw [show z = -2 * y + 5 by linarith [eq3]] at h''
    nlinarith [sq_nonneg (y - 4), sq_nonneg (x - 10), sq_nonneg (z + 3)]
  have eqx : x = 10 := by
    nlinarith [eq1, eqy]
  have eqz : z = -3 := by
    nlinarith [eq3, eqy]
  simp [Prod.ext_iff, eqx, eqy, eqz]
  <;> tauto