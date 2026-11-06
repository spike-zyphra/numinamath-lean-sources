import Mathlib

theorem algebra_267551 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x + y + x * y = 8) (h2 : y + z + y * z = 15) (h3 : z + x + z * x = 35) :
    x + y + z + x * y = 15 := by

  have eq1 : (1 + x) * (1 + y) = 9 := by
    nlinarith

  have eq2 : (1 + y) * (1 + z) = 16 := by
    nlinarith

  have eq3 : (1 + z) * (1 + x) = 36 := by
    nlinarith

  have eq4 : (1 + x) = 9 / 2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, eq1, eq2, eq3]

  have eq5 : (1 + y) = 2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, eq1, eq2, eq3]

  have eq6 : (1 + z) = 8 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, eq1, eq2, eq3]

  have hx2 : x = 7 / 2 := by
    nlinarith [eq4]

  have hy2 : y = 1 := by
    nlinarith [eq5]

  have hz2 : z = 7 := by
    nlinarith [eq6]

  rw [hx2, hy2, hz2]
  norm_num