import Mathlib

theorem algebra_154147 (x y z : ℝ) (h₀ : (x + 3) / 1 = (y - 2) / -5) (h₁ : (y - 2) / -5 = (z + 2) / 3)
    (h₂ : 5 * x - y + 4 * z + 3 = 0) :
    x = -2 ∧ y = -3 ∧ z = 1 := by 
  have eq4 : y = -5 * x - 13 := by 
    linarith
  have eq5 : 3 * y + 5 * z + 4 = 0 := by 
    have h3 : (y - 2) / -5 = (z + 2) / 3 := by 
      linarith
    field_simp at h3 
    linarith 
  have eq6 : 5 * x + 2 * z = -8 := by 
    rw [eq4] at h₂ 
    linarith 
  have eq7 : z = 3 * x + 7 := by 
    rw [eq4] at eq5 
    linarith 
  have hx : x = -2 := by 
    rw [eq7] at eq6
    linarith 
  have hy : y = -3 := by 
    rw [hx] at eq4 
    linarith 
  have hz : z = 1 := by 
    rw [hx] at eq7 
    linarith 
  exact ⟨hx, hy, hz⟩