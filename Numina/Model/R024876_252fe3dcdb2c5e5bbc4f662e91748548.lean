import Mathlib

theorem algebra_208350 {x y : ℕ} (hy : y ≠ 0) (h1 : x + y = 4 * x) (h2 : x + y = 3 * y) :
    y / x = 2 := by 
  have eq1 : y = 3 * x := by 
    omega
  have hx : x = 0 := by
    omega
  have hy' : y = 0 := by
    omega
  contradiction