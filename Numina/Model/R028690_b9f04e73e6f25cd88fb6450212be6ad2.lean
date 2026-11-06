import Mathlib

theorem algebra_108863 (a b c d : ℝ) (h₀ : a + b + c + d = 2014)
    (h₁ : d = a + 16) (h₂ : d = b - 16) (h₃ : d = c / 16) :
    a = 90 ∧ b = 122 ∧ c = 1696 ∧ d = 106 := by
  have eq1 : a = d - 16 := by 
    linarith [h₁]
  have eq2 : b = d + 16 := by 
    linarith [h₂]
  have eq3 : c = 16 * d := by 
    linarith [h₃]
  have eq4 : d = 106 := by 
    rw [eq1, eq2, eq3] at h₀
    linarith
  have ha : a = 90 := by
    linarith [eq1, eq4]
  have hb : b = 122 := by 
    linarith [eq2, eq4]
  have hc : c = 1696 := by 
    linarith [eq3, eq4]
  have hd : d = 106 := by 
    linarith [eq4]
  exact ⟨ha, hb, hc, hd⟩