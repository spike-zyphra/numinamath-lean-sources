import Mathlib

theorem algebra_1557 {a b c : ℝ} (h : a + b + c = 0) : (a + b - c)^3 + (b + c - a)^3 + (a + c - b)^3 = -24*a*b*c := by 
  have h1 : a + b - c = -2 * c := by 
    linarith
  have h2 : b + c - a = -2 * a := by 
    linarith
  have h3 : a + c - b = -2 * b := by 
    linarith

  rw [h1, h2, h3]

  have h4 : (-2 * c) ^ 3 + (-2 * a) ^ 3 + (-2 * b) ^ 3 = -8 * (a^3 + b^3 + c^3) := by 
    ring
  rw [h4]

  have h5 : a^3 + b^3 + c^3 = 3 * a * b * c := by 
    have h5 : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + a * c + b * c)) := by 
      ring
    rw [h] at h5 
    have h6 : a^3 + b^3 + c^3 - 3 * a * b * c = 0 := by 
      linarith 
    linarith

  rw [h5]
  <;> ring