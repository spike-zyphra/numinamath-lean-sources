import Mathlib

theorem algebra_182 (x : ℝ) (hx : x + 3 ≠ 0) (h : (x + 4) / (x + 3) = 4) : 1 / (x + 3) = 3 := by 
  have eq1 : x + 4 = 4 * (x + 3) := by
    have h1 : x + 3 ≠ 0 := hx
    field_simp [h1] at h 
    linarith
  have eq2 : x + 3 = 1 / 3 := by
    linarith
  rw [eq2]
  norm_num