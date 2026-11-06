import Mathlib

theorem algebra_164399 (x y z : ℕ) (h : x ≤ 100) (h' : y ≤ 100) (h'' : z ≤ 100)
    (h''' : (x + y + z) / 3 = 92) (h'''' : y = x + 4) :
    x ≥ 86 := by 
  omega