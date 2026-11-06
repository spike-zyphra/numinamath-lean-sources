import Mathlib

theorem algebra_103331 {x y z : ℝ} (hsum : x + y + z ≠ 0) (h : (x + y + z)^2 = 3 + 3 * (x * y + y * z + z * x)) :
    (x^3 + y^3 + z^3 - 3 * x * y * z) / (x + y + z) = 3 := by
  have h1 : x^3 + y^3 + z^3 - 3 * x * y * z = (x + y + z) * (x^2 + y^2 + z^2 - (x * y + y * z + z * x)) := by
    ring
  have h2 : (x^3 + y^3 + z^3 - 3 * x * y * z) / (x + y + z) = x^2 + y^2 + z^2 - (x * y + y * z + z * x) := by
    rw [h1]
    field_simp [hsum]
  have h3 : x^2 + y^2 + z^2 - (x * y + y * z + z * x) = 3 := by
    have h4 : (x + y + z) ^ 2 = x^2 + y^2 + z^2 + 2 * (x * y + y * z + z * x) := by 
      ring
    have h5 : x^2 + y^2 + z^2 + 2 * (x * y + y * z + z * x) = 3 + 3 * (x * y + y * z + z * x) := by 
      linarith [h, h4]
    linarith 
  rw [h2]
  linarith [h3]