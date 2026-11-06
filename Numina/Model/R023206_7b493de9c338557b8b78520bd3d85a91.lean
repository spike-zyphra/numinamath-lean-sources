import Mathlib

theorem algebra_4822 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : (3 / x + 2 / y + 1 / z) = 6) (h2 : (12 / (x * y) - 1 / z^2) = 36) :
    (x + y) / z = -5 := by

  have eq3 : 3 * (1 / x) + 2 * (1 / y) + (1 / z) = 6 := by
    field_simp [hx, hy, hz] at h1 ⊢
    nlinarith

  have eq4 : 12 * (1 / x) * (1 / y) - (1 / z) ^ 2 = 36 := by
    field_simp [hx, hy, hz] at h2 ⊢
    nlinarith

  have eq5 : 1 / z = 6 - 3 * (1 / x) - 2 * (1 / y) := by
    linarith [eq3]

  rw [eq5] at eq4

  have h3 : ( (1 / x) - 2 ) ^ 2 = 0 := by
    nlinarith [sq_nonneg ((1 / x) - 2), sq_nonneg ((1 / y) - 3), sq_nonneg ((1 / x) - (1 / y)), sq_nonneg ((1 / x) ^ 2 - 4), sq_nonneg ((1 / y) ^ 2 - 9) ]

  have ha1 : (1 / x) = 2 := by
    nlinarith [h3]

  have ha2 : (1 / y) = 3 := by
    nlinarith [ha1, eq4, sq_nonneg ((1 / y) - 3) ]

  have ha3 : (1 / z) = -6 := by
    rw [ha1, ha2] at eq5
    linarith [eq5]

  have hx2 : x = 1 / 2 := by
    have h11 : x ≠ 0 := hx
    field_simp at ha1 ⊢
    linarith

  have hy2 : y = 1 / 3 := by
    have h11 : y ≠ 0 := hy
    field_simp at ha2 ⊢
    linarith

  have hz2 : z = -1 / 6 := by
    have h11 : z ≠ 0 := hz
    field_simp at ha3 ⊢
    nlinarith

  rw [hx2, hy2, hz2]
  norm_num