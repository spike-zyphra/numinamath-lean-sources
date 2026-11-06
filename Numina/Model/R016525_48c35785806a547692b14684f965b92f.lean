import Mathlib

theorem algebra_195002 {a u : ℝ} (ha : a ≠ 0) (hu : u ≠ 0)
    (h1 : 3 / a + 1 / u = 7 / 2) (h2 : 2 / a - 3 / u = 6) :
    a = 2 / 3 := by
  have eq1 : 3 * u + a = (7 / 2) * (a * u) := by
    field_simp [ha, hu] at h1
    nlinarith
  have eq2 : 2 * u - 3 * a = 6 * (a * u) := by 
    field_simp [ha, hu] at h2
    nlinarith
  nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hu, sq_nonneg (a - 2 / 3), sq_nonneg (u + 1)]