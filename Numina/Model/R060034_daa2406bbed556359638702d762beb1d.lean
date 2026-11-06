import Mathlib

theorem algebra_19903 {x : ℝ} (hx : x ≠ -6) (h : (9 - 4 * x) / (x + 6) = 7) : x = -3 := by
  have h1 : x + 6 ≠ 0 := by
    intro h2
    apply hx
    linarith
  have h2 : 9 - 4 * x = 7 * (x + 6) := by
    field_simp [h1] at h 
    linarith
  linarith