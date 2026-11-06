import Mathlib

theorem algebra_213338 {a : ℝ} (ha : a ≠ 0) (h : a / 3 - 3 / a = 2) :
    (a ^ 12 + 729 ^ 2) / (729 * a ^ 6) = 198 := by
  have eq1 : a^2 - 6 * a - 9 = 0 := by
    field_simp at h
    nlinarith
  have eq4 : a^3 = 45 * a + 54 := by
    nlinarith [sq_nonneg (a^2 - 6 * a - 9)]
  have eq5 : a^6 = 17010 * a + 21141 := by
    have h1 : a^3 = 45 * a + 54 := eq4
    have h2 : a^6 = (a^3)^2 := by ring
    rw [h2, h1]
    nlinarith [sq_nonneg (a^2 - 6 * a - 9)]
  have eq6 : a^12 = (a^6)^2 := by ring
  rw [eq6]
  field_simp [ha]
  nlinarith [eq1, eq4, eq5]