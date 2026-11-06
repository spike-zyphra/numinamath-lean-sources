import Mathlib

theorem algebra_110603 {x y : ℤ} (hy : y ≠ 0) (h : x + y = 122) (h' : (x - 19) * 5 = y - 19) :
    x / y = 33 / 89 := by
  have hx : x = 33 := by 
    linarith
  have hy' : y = 89 := by 
    rw [hx] at h 
    linarith
  rw [hx, hy']
  all_goals tauto