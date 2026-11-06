import Mathlib

theorem algebra_167611 {a b c m : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a + b + c = m) (h2 : a^2 + b^2 + c^2 = m^2 / 2) :
    (a * (m - 2 * a)^2 + b * (m - 2 * b)^2 + c * (m - 2 * c)^2) / (a * b * c) = 12 := by

  have h4 : a * b + b * c + c * a = m^2 / 4 := by
    have h : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by ring
    rw [h1, h2] at h
    linarith

  have h5 : a^3 + b^3 + c^3 = m^3 / 4 + 3 * (a * b * c) := by
    have h6 : a^3 + b^3 + c^3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b * c) := by ring
    rw [h6, h1, h4]
    ring

  have h6 : a * (m - 2 * a) ^ 2 + b * (m - 2 * b) ^ 2 + c * (m - 2 * c) ^ 2 = 12 * (a * b * c) := by
    have eq1 : a * (m - 2 * a) ^ 2 + b * (m - 2 * b) ^ 2 + c * (m - 2 * c) ^ 2 =
      (m^2) * (a + b + c) - 4 * m * (a^2 + b^2 + c^2) + 4 * (a^3 + b^3 + c^3) := by
      ring
    rw [eq1]
    rw [h1, h2, h5]
    linarith

  have eq3 : (a * (m - 2 * a) ^ 2 + b * (m - 2 * b) ^ 2 + c * (m - 2 * c) ^ 2) / (a * b * c) = 12 := by
    rw [h6]
    have eq4 : a * b * c ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hb
      exact hc
    field_simp [eq4]
    <;> ring
  exact eq3