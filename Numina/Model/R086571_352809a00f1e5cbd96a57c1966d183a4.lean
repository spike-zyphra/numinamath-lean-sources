import Mathlib

theorem algebra_4582 {a y : ℝ} (h : 6-49*y ≠ 0) (h1 : a+1/(6-49*y)=6) (h2 : a-1/(6-49*y)=8) : a*y = 1 := by 
  have eq1 : a = 7 := by 
    have h3 : a + 1/(6 - 49*y) = 6 := h1
    have h4 : a - 1/(6 - 49*y) = 8 := h2 
    have eq1 : 1/(6 - 49*y) = 6 - a := by 
      field_simp [(show 6 - 49*y ≠ 0 by exact h)] at h3 ⊢ 
      linarith 
    have eq2 : 1/(6 - 49*y) = a - 8 := by 
      field_simp [(show 6 - 49*y ≠ 0 by exact h)] at h4 ⊢ 
      linarith 
    have h6 : 6 - a = a - 8 := by 
      linarith [eq1, eq2] 
    linarith 
  have h7 : 1/(6 - 49*y) = -1 := by 
    rw [eq1] at h1 
    field_simp [(show 6 - 49*y ≠ 0 by exact h)] at h1 ⊢ 
    linarith 
  have h8 : 6 - 49*y = -1 := by 
    have h9 : 6 - 49*y ≠ 0 := h 
    field_simp [(show 6 - 49*y ≠ 0 by exact h)] at h7 
    linarith 
  have hy : y = 1/7 := by 
    linarith 
  rw [eq1, hy] 
  norm_num