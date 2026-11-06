import Mathlib

theorem algebra_138003 (x y z : ℝ) (h1 : (x - 1) / (-1) = (y + 5) / 4) (h2 : (y + 5) / 4 = (z - 1) / 2)
    (h3 : x - 3 * y + 7 * z - 24 = 0) :
    (x, y, z) = (0, -1, 3) := by 
  have eq1 : 4 * x + y = -1 := by 
    field_simp at h1 
    linarith 
  have eq2 : z = (y + 7) / 2 := by 
    field_simp at h2 
    linarith 
  have eq5 : 2 * x + y = -1 := by 
    rw [eq2] at h3 
    linarith 
  have h4 : x = 0 := by 
    linarith [eq1, eq5] 
  have h5 : y = -1 := by 
    rw [h4] at eq1 
    linarith 
  have h6 : z = 3 := by 
    rw [h5] at eq2 
    linarith 
  simp [Prod.ext_iff, h4, h5, h6]