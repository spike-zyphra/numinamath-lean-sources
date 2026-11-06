import Mathlib

theorem number_theory_644 {x : ℕ} (hx1 : x % 3 = 2) (hx2 : (x / 3) % 3 = 2) (hx3 : (x / 9) % 3 = 2) :
    x ≥ 23 := by 
  omega