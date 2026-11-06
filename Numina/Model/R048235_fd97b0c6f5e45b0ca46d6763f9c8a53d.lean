import Mathlib

theorem algebra_285501 {x y : ℕ} (hx : x + y = 10) (hy : x + 8 = y + 10) :
    x = 6 ∧ y = 4 := by 
  have eq2 : y = 4 := by 
    omega 
  have eq3 : x = 6 := by 
    omega 
  exact ⟨eq3, eq2⟩