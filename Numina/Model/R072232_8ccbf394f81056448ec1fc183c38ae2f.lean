import Mathlib

theorem algebra_12035 (x : ℝ) (hx : x ≠ 1) (h : (3 * x - 1) / (4 * x - 4) = 2 / 3) :
    x = -5 := by 
  have h1 : 4 * x - 4 ≠ 0 := by
    intro h2
    apply hx
    linarith
  have eq1 : 3 * (3 * x - 1) = 2 * (4 * x - 4) := by
    field_simp [h1] at h
    linarith
  linarith