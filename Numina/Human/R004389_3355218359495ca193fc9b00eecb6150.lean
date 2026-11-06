import Mathlib

theorem number_theory_259691 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h1 : (9 * x + y) / 12 = y) (h2 : (9 * y + x) / 12 = x) :
    x = 18 ∧ y = 18 := by 
  omega