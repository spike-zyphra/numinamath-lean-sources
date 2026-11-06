import Mathlib

theorem algebra_299022 {m n x y a b : ℝ} (hmn : m^2 + n^2 = 1) (h1 : m * x + n * y = a)
    (h2 : n * x - m * y = b) : x^2 + y^2 = a^2 + b^2 := by
  have eq1 : (m * x + n * y) ^ 2 + (n * x - m * y) ^ 2 = a^2 + b^2 := by
    rw [h1, h2]
  have eq2 : (m * x + n * y) ^ 2 + (n * x - m * y) ^ 2 = (m^2 + n^2) * (x^2 + y^2) := by
    ring_nf
  rw [eq2] at eq1
  rw [hmn] at eq1
  linarith