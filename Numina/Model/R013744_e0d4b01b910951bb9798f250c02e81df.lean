import Mathlib

theorem algebra_12012 {a b c m : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a + b + c = m) (h2 : a^2 + b^2 + c^2 = m^2 / 2) :
    (a * (m - 2 * a)^2 + b * (m - 2 * b)^2 + c * (m - 2 * c)^2) / (a * b * c) = 12 := by

  -- First compute ab + bc + ca
  have h4 : a * b + b * c + c * a = m^2 / 4 := by
    have eq1 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by
      ring
    rw [h1, h2] at eq1
    linarith

  -- Then compute a^3 + b^3 + c^3
  have h5 : a^3 + b^3 + c^3 = m^3 - 3 * m * (a * b + b * c + c * a) + 3 * (a * b * c) := by
    have eq1 : a^3 + b^3 + c^3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b * c) := by
      ring
    rw [h1] at eq1
    linarith

  -- Now prove the identity for the numerator
  have eq1 : a * (m - 2 * a)^2 + b * (m - 2 * b)^2 + c * (m - 2 * c)^2 = 12 * (a * b * c) := by
    have eq2 : a * (m - 2 * a)^2 + b * (m - 2 * b)^2 + c * (m - 2 * c)^2 =
        (a + b + c) * m^2 - 4 * (a^2 + b^2 + c^2) * m + 4 * (a^3 + b^3 + c^3) := by
      ring
    rw [eq2]
    rw [h1, h2, h5, h4]
    ring

  -- Now dividing by non-zero abc
  field_simp [ha, hb, hc]
  linarith [eq1]