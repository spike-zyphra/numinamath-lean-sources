import Mathlib

theorem algebra_19268 (a : ℕ → ℤ) (ha0 : a 0 = 2222) (han : ∀ n, a (n + 1) = a n + 1010) :
    a 5 + a 6 = 15554 := by
  have ha1 : a 1 = a 0 + 1010 := han 0
  rw [ha0] at ha1
  have ha2 : a 2 = a 1 + 1010 := han 1
  rw [ha1] at ha2
  have ha3 : a 3 = a 2 + 1010 := han 2
  rw [ha2] at ha3
  have ha4 : a 4 = a 3 + 1010 := han 3
  rw [ha3] at ha4
  have ha5 : a 5 = a 4 + 1010 := han 4
  rw [ha4] at ha5
  have ha6 : a 6 = a 5 + 1010 := han 5
  rw [ha5] at ha6
  rw [ha5, ha6]
  all_goals norm_num
  all_goals linarith