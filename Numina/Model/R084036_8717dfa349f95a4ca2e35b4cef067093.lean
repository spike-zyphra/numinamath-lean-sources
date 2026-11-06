import Mathlib

theorem algebra_12510 (A B C D E F G H : ℝ)
    (h₀ : C = 5) (h₁ : A + B + C = 30) (h₂ : B + C + D = 30)
    (h₃ : C + D + E = 30) (h₄ : D + E + F = 30) (h₅ : E + F + G = 30)
    (h₆ : F + G + H = 30) :
    A + H = 25 := by
  rw [h₀] at h₁ h₂ h₃ -- Substitute C = 5 into equations h₁, h₂, h₃
  have eq1 : A + B = 25 := by 
    linarith
  have eq2 : B + D = 25 := by 
    linarith
  have eq3 : D + E = 25 := by 
    linarith
  have eq4 : F = 5 := by
    linarith [h₄, eq3]
  have eq5 : G + H = 25 := by 
    linarith [h₆, eq4]
  have eq6 : E + G = 25 := by 
    linarith [h₅, eq4]
  have eq7 : E = H := by 
    linarith [eq5, eq6]
  have eq8 : A = D := by 
    linarith [eq1, eq2]
  linarith [eq8, eq3, eq7]