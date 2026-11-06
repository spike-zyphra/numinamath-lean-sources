import Mathlib

theorem algebra_129326 (x y z : ℝ) (h : (x + 3) / 2 = (y - 1) / 3 ∧ (y - 1) / 3 = (z - 1) / 5)
    (h' : 2 * x + 3 * y + 7 * z - 52 = 0) :
    x = -1 ∧ y = 4 ∧ z = 6 := by
  rcases h with ⟨h1, h2⟩
  have eq1 : (x + 3) / 2 = (y - 1) / 3 := h1
  have eq2 : (y - 1) / 3 = (z - 1) / 5 := h2

  have eq3 : 3 * (x + 3) = 2 * (y - 1) := by
    field_simp at eq1 ⊢
    linarith
  
  have eq4 : 5 * (y - 1) = 3 * (z - 1) := by
    field_simp at eq2 ⊢
    linarith
  
  have eq5 : 2 * y = 3 * x + 11 := by
    linarith [eq3]

  have eq6 : 3 * z = 5 * y - 2 := by
    linarith [eq4]

  have eq9 : 2 * x + 3 * y + 7 * z - 52 = 0 := by 
    linarith [h']

  have eq10 : y = (3 * x + 11) / 2 := by 
    linarith [eq5]

  have eq11 : z = (15 * x + 51) / 6 := by 
    have eq12 : 3 * z = 5 * y - 2 := by linarith [eq6]
    rw [eq10] at eq12
    linarith

  have hx : x = -1 := by 
    rw [eq10, eq11] at eq9
    linarith

  have hy : y = 4 := by 
    rw [hx] at eq5
    linarith

  have hz : z = 6 := by 
    rw [hy] at eq6
    linarith
  
  exact ⟨hx, hy, hz⟩