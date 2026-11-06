import Mathlib

theorem algebra_242383 {x y : ℝ} (hxy : x * (y + 2) = 100 ∧ y * (x + 2) = 60) : x - y = 20 := by
  have h1 : x * (y + 2) = 100 := hxy.1
  have h2 : y * (x + 2) = 60 := hxy.2
  have eq1 : x * y + 2 * x = 100 := by
    linarith [h1]
  have eq2 : x * y + 2 * y = 60 := by
    linarith [h2]
  have eq3 : 2 * x - 2 * y = 40 := by
    linarith [eq1, eq2]
  have eq4 : x - y = 20 := by
    linarith
  exact eq4