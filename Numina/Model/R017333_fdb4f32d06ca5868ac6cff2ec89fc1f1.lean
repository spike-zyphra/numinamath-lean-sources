import Mathlib

theorem algebra_166700 (v : ℝ) (h : v > 0) (h1 : 1 / v + 25 / v + 4 / v = 1.25) (h2 : 1 / (16 * v) + 25 / (49 * v) + 4 / (49 * v) = 5 / 4) :
    v = 5 / 7 := by
  have eq1 : 30 / v = 1.25 := by
    have h' : 1 / v + 25 / v + 4 / v = 30 / v := by 
      field_simp 
      <;> ring 
    rw [h'] at h1 
    all_goals linarith 
  have eq2 : v = (30 : ℝ) / 1.25 := by
    have h' : v ≠ 0 := by linarith
    field_simp at eq1 ⊢
    linarith
  have eq3 : v = (24 : ℝ) := by
    rw [eq2]
    norm_num
  have eq4 : 1 / (16 * v) + 25 / (49 * v) + 4 / (49 * v) = 5 / 4 := h2
  rw [eq3] at eq4
  norm_num at eq4
  all_goals nlinarith