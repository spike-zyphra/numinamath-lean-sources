import Mathlib

theorem algebra_14180 {x : ℝ} (hx : x ≠ 0) (h : (x / 3 - 11) = x / 5) :
    x = 82.50 := by
  have eq1 : x / 3 - x / 5 = 11 := by
    linarith
  have eq2 : 2 * x = 165 := by
    field_simp at eq1 ⊢
    linarith
  have hx2 : x = 165 / 2 := by
    linarith
  rw [hx2]
  norm_num