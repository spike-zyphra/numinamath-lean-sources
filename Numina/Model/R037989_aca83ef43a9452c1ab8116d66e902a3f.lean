import Mathlib

theorem algebra_198687 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x + 1 / y = -2) (h2 : y + 1 / z = -1 / 2) (h3 : 1 / x + z = 1) :
    (x, y, z) = (-1, -1, 2) := by

  have eq1 : x * y + 1 = -2 * y := by
    have h1' : x + 1 / y = -2 := h1
    field_simp [hy] at h1' ⊢
    linarith

  have eq2 : y * z + 1 = -1 / 2 * z := by
    have h2' : y + 1 / z = -1 / 2 := h2
    field_simp [hz] at h2' ⊢
    linarith

  have eq3 : 1 + x * z = x := by
    have h3' : 1 / x + z = 1 := h3
    field_simp [hx] at h3' ⊢
    linarith
  
  have eq4 : x * z = x - 1 := by linarith

  have eq5 : x = -1 := by 
    nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show y ≠ 0 by exact hy), sq_pos_of_ne_zero (show z ≠ 0 by exact hz), sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (z - 2), sq_nonneg (x * y), sq_nonneg (x * z), sq_nonneg (y * z)]

  have eq6 : z = 2 := by
    rw [eq5] at eq4
    nlinarith

  have eq7 : y = -1 := by
    rw [eq5] at eq1
    nlinarith

  simp [Prod.ext_iff, eq5, eq7, eq6]