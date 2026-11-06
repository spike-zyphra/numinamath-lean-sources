import Mathlib

theorem algebra_15126 (x : ℝ) (hx : x ≠ 0) : (4 / (3 / x ^ 3)) * (3 * x ^ 2 / 2) = 2 * x ^ 5 := by 
  field_simp [hx]
  <;> ring