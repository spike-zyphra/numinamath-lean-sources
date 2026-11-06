import Mathlib

theorem algebra_141997 {x y z : ℤ} (h1 : x + y = z) (h2 : 2 * z = x + 3) (h3 : 2 * x + 2 * y = z + 5) :
    x = 7 ∧ y = -2 ∧ z = 5 := by 
  have h4 : y = -2 := by 
    omega
  have h5 : x = 7 := by 
    omega
  have h6 : z = 5 := by 
    linarith [h1, h4, h5]
  exact ⟨h5, h4, h6⟩