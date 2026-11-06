import Mathlib

theorem algebra_281402 {x y z : ℕ} (h1 : x = 2 * y) (h2 : z = y + 20) (h3 : x + y + z = 180) (h4 : y + z = 180) :
    x = 48 ∧ y = 60 ∧ z = 80 := by 
  omega