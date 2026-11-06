import Mathlib

theorem algebra_327859 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a + b + c = 0) :
    a * (1 / b + 1 / c) + b * (1 / c + 1 / a) + c * (1 / a + 1 / b) = -3 := by

  have eq1 : a * (1 / b + 1 / c) + b * (1 / c + 1 / a) + c * (1 / a + 1 / b) =
      (a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b)) / (a * b * c) := by
    field_simp [hb, hc, ha]
    ring

  have eq2 : a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) = - (a^3 + b^3 + c^3) := by
    have eq3 : b + c = -a := by linarith
    have eq4 : a + c = -b := by linarith
    have eq5 : a + b = -c := by linarith
    rw [eq3, eq4, eq5]
    all_goals ring

  have eq3 : a^3 + b^3 + c^3 = 3 * a * b * c := by
    have eq4 : a + b + c = 0 := h
    have eq5 : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - a * b - a * c - b * c) := by
      ring
    rw [show (a + b + c ) = (0 : ℝ) by linarith] at eq5
    linarith

  have eq4 : (a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b)) / (a * b * c) = -3 := by
    rw [eq2]
    rw [eq3]
    field_simp [hb, hc, ha]
    <;> nlinarith

  rw [eq1]
  rw [eq4]