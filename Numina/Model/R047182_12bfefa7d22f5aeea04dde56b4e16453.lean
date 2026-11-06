import Mathlib

theorem algebra_3457 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hn : x^2 - y^2 ≠ 0) : (x^3 * y^2 - x^2 * y^3) * (x + y) / ((x * y)^3 * (x^2 - y^2)) = 1 / (x * y) := by 
  have eq1 : (x^3 * y^2 - x^2 * y^3) * (x + y) = x^2 * y^2 * (x^2 - y^2) := by
    ring_nf
  rw [eq1]
  have eq2 : (x^2 * y^2 * (x^2 - y^2)) / ((x * y)^3 * (x^2 - y^2)) = (x^2 * y^2) / (x * y)^3 := by
    field_simp [(show (x^2 - y^2 : ℝ) ≠ 0 by assumption), hx, hy]
    <;> ring
  rw [eq2]
  have eq3 : (x^2 * y^2) / (x * y)^3 = 1 / (x * y) := by
    field_simp [(show (x : ℝ) ≠ 0 by assumption), (show (y : ℝ) ≠ 0 by assumption)]
    <;> ring_nf
  rw [eq3]