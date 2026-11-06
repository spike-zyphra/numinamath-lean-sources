import Mathlib

theorem algebra_293468 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0) (h : x / y + y / z + z / x = x / z + z / y + y / x + 1) :
    x / y + y / z + z / x = -1 := by
  have hz1 : z = -x - y := by
    linarith
  have h1 : x / y + y / z + z / x = x / z + z / y + y / x + 1 := h
  have eq3 : x^2 * z + x * y^2 + y * z^2 = x^2 * y + x * z^2 + y^2 * z + x * y * z := by 
    have eq4 : (x / y + y / z + z / x) = x / z + z / y + y / x + 1 := h
    have eq5 : (x / y + y / z + z / x) * (x * y * z) = (x / z + z / y + y / x + 1) * (x * y * z) := by 
      rw [eq4]
    have eq6 : (x / y + y / z + z / x) * (x * y * z) = x^2 * z + x * y^2 + y * z^2 := by 
      field_simp [hx, hy, hz]
      <;> ring
    have eq7 : (x / z + z / y + y / x + 1) * (x * y * z) = x^2 * y + x * z^2 + y^2 * z + x * y * z := by
      field_simp [hx, hy, hz]
      <;> ring
    linarith [eq5, eq6, eq7]
  have eq8 : x^2 * z + x * y^2 + y * z^2 = x^2 * y + x * z^2 + y^2 * z + x * y * z := eq3
  rw [show z = -x - y by linarith] at eq8
  have eq9 : x / y + y / z + z / x = -1 := by 
    rw [show z = -x - y by linarith]
    field_simp [(show x ≠ 0 by exact hx), (show y ≠ 0 by exact hy), 
      (show (-x - y : ℝ) ≠ 0 by 
        intro h
        apply hz
        linarith
      )
    ]
    <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x * y), sq_nonneg ((x - y) * (x + y)), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_pos_of_ne_zero (show (-x - y : ℝ) ≠ 0 by intro h; apply hz; linarith)]
  linarith [eq9]