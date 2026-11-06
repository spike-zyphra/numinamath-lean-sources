import Mathlib

theorem algebra_6535 (m : ℝ) (x y z : ℝ) (h₁ : x = (m + 9) / 2) (h₂ : y = (2 * m + 15) / 2)
    (h₃ : z = (3 * m + 18) / 2) :
    ((x + y + z) / 3) = m + 7 := by 
  linarith