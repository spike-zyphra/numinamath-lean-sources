import Mathlib

theorem algebra_210848 (x y z : ℕ) (h₀ : x < y) (h₁ : y < z)
    (h₂ : z - x = y - z) (h₃ : y - x = 6) (h₄ : z^2 - x^2 = 432) :
    x = 12 ∧ y = 18 ∧ z = 24 := by
  have h5 : y = x + 6 := by 
    omega
  have h6 : z = x + 3 := by
    omega
  -- contradiction of z < y with hypothesis y < z
  have h7 : z < y := by 
    omega
  linarith