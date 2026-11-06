import Mathlib

theorem algebra_249766 (A P M F : ℕ)
    (hA : A + 2 = P - 2) (hP : P - 2 = M * 2) (hM : M * 2 = F / 2)
    (h : A + P + M + F = 90) :
    A = 18 ∧ P = 22 ∧ M = 10 ∧ F = 40 := by 
  have h_eq1 : A = 18 := by 
    omega 
  have h_eq2 : P = 22 := by 
    omega 
  have h_eq3 : M = 10 := by 
    omega 
  have h_eq4 : F = 40 := by 
    omega 
  exact ⟨h_eq1, h_eq2, h_eq3, h_eq4⟩