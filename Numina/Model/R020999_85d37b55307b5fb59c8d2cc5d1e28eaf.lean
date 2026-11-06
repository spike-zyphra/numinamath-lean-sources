import Mathlib

theorem algebra_299779 {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hx : x ≠ 0)
    (h1 : x + 1 / y = 4) (h2 : y + 1 / z = 1) (h3 : z + 1 / x = 7 / 3) :
    x * y * z = 1 := by

  have eq1 : x * y + 1 = 4 * y := by
    have h4 : y ≠ 0 := hy
    field_simp at h1
    linarith

  have eq2 : y * z + 1 = z := by
    have h5 : z ≠ 0 := hz
    field_simp at h2
    linarith

  have eq3 : 3 * z * x + 3 = 7 * x := by
    have h6 : x ≠ 0 := hx
    field_simp at h3
    linarith

  have eq4 : (3 * z - 5) ^ 2 = 0 := by
    nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by tauto), sq_pos_of_ne_zero (show y ≠ 0 by tauto), sq_pos_of_ne_zero (show z ≠ 0 by tauto), sq_nonneg (x * y * z - 1), sq_nonneg (y - 2 / 5), sq_nonneg (z - 5 / 3), sq_nonneg (x - 3 / 2)]

  have hz' : z = 5 / 3 := by
    nlinarith [eq4]

  have hy' : y = 2 / 5 := by 
    rw [hz'] at eq2
    nlinarith

  have hx' : x = 3 / 2 := by 
    rw [hy'] at eq1
    linarith

  rw [hx', hy', hz']
  norm_num