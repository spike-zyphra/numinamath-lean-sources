import Mathlib

theorem number_theory_151190 {x y z : ℕ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x * 100 + y * 10 + z = 15918) (h1 : x + y + z = 24) :
    x * 4444 + y * 4444 + z = 10666612 := by 
  omega