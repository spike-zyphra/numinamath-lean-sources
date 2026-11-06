import Mathlib

theorem algebra_194416 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : 825 / x = 825 / y - 1) (h2 : 825 / x = 825 / y - 220) :
    x = 2 ∧ y = 1000 := by 
  linarith