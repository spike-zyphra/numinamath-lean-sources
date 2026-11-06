import Mathlib

theorem algebra_142748 {x : ℝ} (hx : x ≠ 0) (h : 25 * (1 + 14 / 100) = x * (1 + 50 / 100)) :
    x = 19 := by
  have h1 : x = 25 * (1 + 14 / 100) / (1 + 50 / 100 : ℝ) := by 
    field_simp at h ⊢ 
    linarith 
  rw [h1] 
  norm_num