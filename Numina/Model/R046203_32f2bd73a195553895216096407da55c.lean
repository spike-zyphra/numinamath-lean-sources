import Mathlib

theorem algebra_186952 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a + b + c = 26) (h2 : 1 / a + 1 / b + 1 / c = 28) :
    a / b + b / c + c / a + a / c + c / b + b / a = 725 := by
  have h3 : b * c + a * c + a * b = 28 * (a * b * c) := by
    field_simp [ha, hb, hc] at h2
    nlinarith [h2]
  
  have h4 : a / b + b / c + c / a + a / c + c / b + b / a =
      ( (a^2 + b^2) * c + (b^2 + c^2) * a + (c^2 + a^2) * b ) / (a * b * c) := by
    field_simp [ha, hb, hc]
    ring

  have h5 : ( (a^2 + b^2) * c + (b^2 + c^2) * a + (c^2 + a^2) * b ) = (a + b + c) * (b * c + a * c + a * b) - 3 * (a * b * c) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]

  rw [h4]
  rw [h5]
  rw [h3]
  rw [h1]

  have h6 : a * b * c ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact ha
    exact hb
    exact hc
  
  field_simp [h6]
  <;> nlinarith