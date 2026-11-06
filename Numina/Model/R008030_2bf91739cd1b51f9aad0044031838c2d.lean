import Mathlib

theorem algebra_142338 {x y : ℝ} (hxy : x ≠ y) (h : x^2 - 2000 * x = y^2 - 2000 * y) : x + y = 2000 := by
  have h1 : x^2 - 2000 * x - (y^2 - 2000 * y) = 0 := by linarith 
  have h2 : (x - y) * (x + y - 2000) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where h3 : x - y = 0, which gives x = y
    exfalso
    apply hxy
    linarith
  · -- Case where h4 : x + y - 2000 = 0, which gives x + y = 2000
    linarith