import Mathlib

theorem algebra_20813 (a b c d e f : ℝ) (h : a = 5) (h' : b = -20) (h'' : c = 9) (h''' : d = -18) (h'''' : e = -16) :
    (-b / (2 * a), -d / (2 * c)) = (2, 1) := by 
  rw [h, h', h'', h''']
  norm_num