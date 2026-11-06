import Mathlib

theorem inequalities_202856 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : |x - y| < 2) (hyz : |y - z| < 2) (hzz : |z - x| < 2) :
    Real.sqrt (x * y + 1) + Real.sqrt (y * z + 1) + Real.sqrt (z * x + 1) > x + y + z := by

  have h1 : (x - y) ^ 2 < 4 := by
    have h1 : -2 < x - y := by linarith [abs_lt.mp hxy]
    have h2 : x - y < 2 := by linarith [abs_lt.mp hxy]
    nlinarith

  have h2 : (y - z) ^ 2 < 4 := by
    have h1 : -2 < y - z := by linarith [abs_lt.mp hyz]
    have h2 : y - z < 2 := by linarith [abs_lt.mp hyz]
    nlinarith

  have h3 : (z - x) ^ 2 < 4 := by
    have h1 : -2 < z - x := by linarith [abs_lt.mp hzz]
    have h2 : z - x < 2 := by linarith [abs_lt.mp hzz]
    nlinarith

  have h4 : Real.sqrt (x * y + 1) > (x + y) / 2 := by
    have h5 : (x * y + 1) > ((x + y) / 2) ^ 2 := by
      nlinarith
    have h6 : Real.sqrt (x * y + 1) > Real.sqrt (((x + y) / 2) ^ 2) := by
      apply Real.sqrt_lt_sqrt
      all_goals nlinarith
    have h7 : Real.sqrt (((x + y) / 2) ^ 2) = (x + y) / 2 := by
      rw [Real.sqrt_sq (by linarith)]
    linarith [h6, h7]

  have h5 : Real.sqrt (y * z + 1) > (y + z) / 2 := by
    have h6 : (y * z + 1) > ((y + z) / 2) ^ 2 := by
      nlinarith
    have h7 : Real.sqrt (y * z + 1) > Real.sqrt (((y + z) / 2) ^ 2) := by
      apply Real.sqrt_lt_sqrt
      all_goals nlinarith
    have h8 : Real.sqrt (((y + z) / 2) ^ 2) = (y + z) / 2 := by
      rw [Real.sqrt_sq (by linarith)]
    linarith [h7, h8]

  have h6 : Real.sqrt (z * x + 1) > (z + x) / 2 := by
    have h7 : (z * x + 1) > ((z + x) / 2) ^ 2 := by
      nlinarith
    have h8 : Real.sqrt (z * x + 1) > Real.sqrt (((z + x) / 2) ^ 2) := by
      apply Real.sqrt_lt_sqrt
      all_goals nlinarith
    have h9 : Real.sqrt (((z + x) / 2) ^ 2) = (z + x) / 2 := by
      rw [Real.sqrt_sq (by linarith)]
    linarith [h8, h9]

  linarith [h4, h5, h6]