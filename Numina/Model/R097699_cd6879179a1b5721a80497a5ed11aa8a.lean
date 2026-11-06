import Mathlib

theorem algebra_213637 {a b c : ℝ} (h : a ≠ 0) (h1 : b ≠ 0) (h2 : c ≠ 0)
    (h3 : a + b + c = 0) :
    a^2 / (b * c) + b^2 / (a * c) + c^2 / (a * b) = 3 := by
  have eq1 : a^2 / (b * c) + b^2 / (a * c) + c^2 / (a * b) =
    (a^3 + b^3 + c^3) / (a * b * c) := by
    field_simp [h, h1, h2, mul_ne_zero (mul_ne_zero h h1), mul_ne_zero (mul_ne_zero h h2), mul_ne_zero h1 h2]
    ring
  have eq2 : a^3 + b^3 + c^3 = 3 * (a * b * c) := by
    have eq3 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + a * c + b * c)) := by
      ring_nf
    rw [h3] at eq3
    have eq4 : a^3 + b^3 + c^3 - 3 * (a * b * c) = 0 := by
      linarith
    linarith
  rw [eq1]
  rw [eq2]
  field_simp [h, h1, h2, mul_ne_zero (mul_ne_zero h h1), mul_ne_zero (mul_ne_zero h h2), mul_ne_zero h1 h2]
  <;> ring