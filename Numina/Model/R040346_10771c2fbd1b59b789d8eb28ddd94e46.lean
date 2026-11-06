import Mathlib

theorem algebra_38514 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x * y + y * z = 30) (h2 : y * z + z * x = 36) (h3 : z * x + x * y = 42) :
    x + y + z = 13 := by 
  have eq1 : x * y = 18 := by
    nlinarith
  have eq2 : y * z = 12 := by
    nlinarith
  have eq3 : z * x = 24 := by 
    nlinarith
  have hz2 : z = 4 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, 
              eq1, eq2, eq3]
  have hx2 : x = 6 := by 
    rw [hz2] at eq3
    nlinarith
  have hy2 : y = 3 := by 
    rw [hx2] at eq1
    nlinarith
  linarith [hx2, hy2, hz2]