import Mathlib

theorem algebra_316465 {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hx : x ≠ 0)
    (h1 : x + 1 / y = 4) (h2 : y + 1 / z = 1) (h3 : z + 1 / x = 7 / 3) :
    x * y * z = 1 := by
  have eq1 : x * y + 1 = 4 * y := by
    have h1' : x + 1 / y = 4 := h1
    field_simp [hy] at h1' ⊢
    linarith
  have eq2 : y * z + 1 = z := by
    have h2' : y + 1 / z = 1 := h2
    field_simp [hz] at h2' ⊢
    linarith
  have eq3 : 3 * (z * x) + 3 = 7 * x := by
    have h3' : z + 1 / x = 7 / 3 := h3
    field_simp [hx] at h3' ⊢
    linarith
  have eq4 : x * y = 4 * y - 1 := by
    linarith [eq1]
  have eq5 : y * z = z - 1 := by 
    linarith [eq2]
  have eq7 : x * y * z = 3 * z - 4 := by 
    have h8 : x * y = 4 * y - 1 := eq4
    calc
      x * y * z = (x * y) * z := by ring
      _ = (4 * y - 1) * z := by rw [h8]
      _ = 4 * (y * z) - z := by ring
      _ = 4 * (z - 1) - z := by rw [eq5]
      _ = 3 * z - 4 := by ring
  have eq8 : x = 3 / 2 := by
    nlinarith [sq_nonneg (x * y), sq_nonneg (x * z), sq_nonneg (y * z), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_pos_of_ne_zero hz, sq_nonneg (x - 3 / 2), sq_nonneg (y - 2 / 5), sq_nonneg (z - 5 / 3)]
  have eq9 : y = 2 / 5 := by 
    rw [eq8] at eq1
    linarith
  have eq10 : z = 5 / 3 := by
    rw [eq8] at eq3
    linarith
  rw [eq8, eq9, eq10]
  norm_num