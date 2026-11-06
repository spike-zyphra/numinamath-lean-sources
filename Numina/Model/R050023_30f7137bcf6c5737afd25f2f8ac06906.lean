import Mathlib

theorem algebra_177157 (x y z : ℝ) (h : (x - 1) / 2 = (y - 3) / 4 ∧ (y - 3) / 4 = z /(-1)) :
    5 * x - 2 * y + 2 * z + 1 = 0 := by 
  rcases h with ⟨h1, h2⟩

  have eq1 : y = 2 * x + 1 := by
    linarith

  have eq2 : z = (1 - x)/2 := by
    have h3 : z = (3 - y)/4 := by
      field_simp at h2 ⊢
      linarith
    rw [h3]
    rw [eq1]
    field_simp
    ring
  
  rw [eq1, eq2]
  linarith