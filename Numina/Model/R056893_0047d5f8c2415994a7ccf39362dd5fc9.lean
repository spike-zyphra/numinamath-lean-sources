import Mathlib

theorem number_theory_262596 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h1 : 60 ∣ 3 * x + 5 * y) (h2 : 60 ∣ 5 * x + 2 * y) :
    60 ∣ 2 * x + 3 * y := by 
  omega