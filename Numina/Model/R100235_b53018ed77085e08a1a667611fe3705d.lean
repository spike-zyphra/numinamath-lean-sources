import Mathlib

theorem algebra_2183 (x : ℝ) (hx : x ≠ 0) :
    1 / x + 1 / (2 * x) + 1 / (3 * x) = 11 / (6 * x) := by 
  field_simp [hx, show 2 * x ≠ 0 by simp [hx], show 3 * x ≠ 0 by simp [hx], show 6 * x ≠ 0 by simp [hx]]
  <;> ring