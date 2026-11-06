import Mathlib

theorem algebra_218932 (a d : ℚ) (h : a = 1.36) (h' : d = 1.52 - 1.36)
    (h'' : a + d = 2.8) (h''' : a + 2 * d = 2.24) (h'''' : a + 3 * d = 2.40)
    (h''''' : a + 4 * d = 2.56) (h'''''' : a + 5 * d = 3 * 12) (h''''''' : a + 6 * d = 3 * 28)
    (h'''''''' : a + 7 * d = 3 * 44) (h''''''''' : a + 8 * d = 4) :
    d = 1 / 6 ∧ a = 1.36 := by 
  rw [h] at h''
  rw [h'] at h''
  norm_num at h''
  all_goals linarith