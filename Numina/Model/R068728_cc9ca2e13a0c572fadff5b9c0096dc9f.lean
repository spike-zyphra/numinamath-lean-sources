import Mathlib

theorem algebra_154846 (x y z : ℝ) (h : (x - 2) / (-1) = (y - 3) / (-1)) (h' : (y - 3) / (-1) = (z + 1) / 4)
    (h'' : x + 2 * y + 3 * z - 14 = 0) :
    x = 1 ∧ y = 2 ∧ z = 3 := by 
  have eq1 : x - y + 1 = 0 := by 
    field_simp at h 
    linarith 
  have eq2 : z + 4 * y - 11 = 0 := by
    field_simp at h' 
    linarith 
  have eq3 : x + 2 * y + 3 * z - 14 = 0 := by 
    linarith 
  have h2 : y = 2 := by 
    have eq4 : z = 5 - y := by
      have eq4 : x = y - 1 := by linarith [eq1] 
      rw [eq4] at h''
      linarith 
    rw [eq4] at eq2 
    linarith 
  have hx : x = 1 := by 
    have eq4 : x = y - 1 := by linarith [eq1] 
    rw [h2] at eq4 
    linarith 
  have hz : z = 3 := by 
    have eq4 : z = 5 - y := by
      have eq4 : x = y - 1 := by linarith [eq1] 
      rw [eq4] at h''
      linarith 
    rw [h2] at eq4 
    linarith 
  exact ⟨hx, h2, hz⟩