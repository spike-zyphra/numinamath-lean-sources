import Mathlib

theorem number_theory_174055 (x y z : ℕ) (h : x + y + z = 26)
    (h1 : x ≥ 20) (h2 : y ≥ 2) (h3 : z ≥ 5) :
    x * 1 + y * 2 + z * 5 = 78 := by 
  omega