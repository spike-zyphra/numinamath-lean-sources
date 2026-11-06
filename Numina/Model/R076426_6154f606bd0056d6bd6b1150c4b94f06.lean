import Mathlib

theorem algebra_27447 (x y z : ℕ) (hx : x + y + z = 45) (hy : 59 * x + 41 * y + 40 * z = 2008) :
    x = 10 ∧ y = 18 ∧ z = 17 := by 
  have h1 : x = 10 := by 
    omega
  have h2 : y = 18 := by 
    omega
  have h3 : z = 17 := by 
    omega
  exact ⟨h1, h2, h3⟩