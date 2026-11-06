import Mathlib

theorem algebra_274039 (a d : ℚ) (h : a + 2 * d + a + 3 * d + a + 9 * d + a + 10 * d = 2002) :
    a + a + 4 * d + a + 6 * d + a + 8 * d + a + 12 * d = 2502.5 := by 
  have eq1 : 4 * a + 24 * d = 2002 := by
    linarith
  have eq2 : a + 6 * d = 500.5 := by
    have : (4 * a + 24 * d) = 2002 := by linarith 
    have : a + 6 * d = (2002 : ℚ) / 4 := by 
      linarith 
    rw [this]
    norm_num 
  have eq3 : a + a + 4 * d + a + 6 * d + a + 8 * d + a + 12 * d = 5 * (a + 6 * d) := by 
    ring 
  rw [eq3] 
  rw [eq2] 
  norm_num