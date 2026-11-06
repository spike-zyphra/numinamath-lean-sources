import Mathlib

theorem algebra_678 (d u : ℝ) (hd : d > 0) (hu : u > 0) (h₁ : d / 20 + u / 35 = 9) (h₂ : u / 20 + d / 35 = 7.5) :
    d + u = 210 ∧ d = 140 := by
  have eq3 : 7 * d + 4 * u = 1260 := by
    linarith
  
  have eq4 : 4 * d + 7 * u = 1050 := by 
    linarith
  
  have h3 : d + u = 210 := by 
    linarith [eq3, eq4]

  have h4 : d = 140 := by 
    linarith [eq3, h3]

  exact ⟨h3, h4⟩