import Mathlib

theorem algebra_17074 {x y : ℤ} (h₁ : 12 * x + 21 * y = 15) (h₂ : 21 * x + 12 * y = 51) :
    (x, y) = (3, -1) := by 
  have hx : x = 3 := by 
    omega
  have hy : y = -1 := by 
    omega
  exact Prod.ext hx hy