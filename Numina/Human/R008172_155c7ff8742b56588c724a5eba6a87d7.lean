import Mathlib

theorem algebra_299022 {m n x y a b : ℝ} (hmn : m^2 + n^2 = 1) (h1 : m * x + n * y = a)
    (h2 : n * x - m * y = b) : x^2 + y^2 = a^2 + b^2 := by 
  have h3 : a^2 = (m * x + n * y) ^ 2 := by rw [h1]
  have h4 : a^2 = m^2 * x^2 + n^2 * y^2 + 2 * m * n * x * y := by
    rw [h3]; ring
  have h5 : b^2 = (n * x - m * y) ^ 2 := by rw [h2]
  have h6 : b^2 = n^2 * x^2 + m^2 * y^2 - 2 * m * n * x * y := by 
    rw [h5]; ring
  have h7 : a^2 + b^2 = (m^2 + n^2) * x^2 + (m^2 + n^2) * y^2 := by 
    linarith
  have h8 : a^2 + b^2 = x^2 + y^2 := by
    rw [h7, hmn]; ring
  linarith