import Mathlib

theorem algebra_140573 {a b c d : ℝ} (h₀ : a + b + c + d = 45) (h₁ : a + 2 = b - 2)
    (h₂ : b - 2 = 2 * c) (h₃ : 2 * c = d / 2) :
    a = 8 ∧ b = 12 ∧ c = 5 ∧ d = 20 := by
  have eq1 : a = b - 4 := by
    linarith
  
  have eq2 : b = 2 * c + 2 := by 
    linarith
  
  have eq3 : d = 4 * c := by
    linarith
  
  have eq4 : a = 2 * c - 2 := by 
    rw [eq2] at eq1
    linarith
  
  have h4 : c = 5 := by
    have eq5 : a + b + c + d = 45 := h₀
    rw [eq4, eq2, eq3] at eq5
    linarith
  
  have ha : a = 8 := by
    rw [h4] at eq4
    linarith
  
  have hb : b = 12 := by
    rw [h4] at eq2
    linarith
  
  have hd : d = 20 := by
    rw [h4] at eq3
    linarith
  
  exact ⟨ha, hb, h4, hd⟩