import Mathlib

theorem algebra_121911 (x y z : ℝ) (h : (x - 1) / 2 = (y - 1) / -1) (h' : (y - 1) / -1 = (z + 2) / 3)
    (h'' : 4 * x + 2 * y - z - 11 = 0) :
    x = 3 ∧ y = 0 ∧ z = 1 := by 
  have eq1 : x + 2 * y = 3 := by 
    linarith 
  have eq2 : 3 * y + z = 1 := by 
    linarith 
  have eq3 : 4 * x + 2 * y - z - 11 = 0 := by 
    linarith 
  have hy : y = 0 := by 
    have eq4 : -6 * y - z = -1 := by 
      have h1 : x = 3 - 2 * y := by linarith [eq1]
      rw [h1] at eq3 
      linarith 
    have h2 : z = 1 - 3 * y := by linarith [eq2]
    rw [h2] at eq4 
    linarith 
  have hx : x = 3 := by 
    linarith [eq1, hy] 
  have hz : z = 1 := by 
    linarith [eq2, hy] 
  exact ⟨hx, hy, hz⟩