import Mathlib

theorem algebra_244672 {f : ℝ → ℝ} (h : ∀ x y, y^3 * f x = x^3 * f y) (hf : f 3 ≠ 0) :
    (f 20 - f 2) / f 3 = 296 := by
  have eq1 := h 20 3
  have eq2 := h 2 3
  norm_num at eq1 eq2
  
  have eq3 : f 20 = (8000 / 27) * f 3 := by
    linarith
  
  have eq4 : f 2 = (8 / 27) * f 3 := by
    linarith
  
  have eq5 : f 20 - f 2 = (7992 / 27) * f 3 := by
    rw [eq3, eq4]
    ring
  
  have eq6 : (f 20 - f 2) / f 3 = (7992 / 27) := by
    rw [eq5]
    field_simp [hf]
    all_goals linarith

  rw [eq6]
  norm_num