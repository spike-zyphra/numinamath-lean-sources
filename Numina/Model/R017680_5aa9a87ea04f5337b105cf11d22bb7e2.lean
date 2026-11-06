import Mathlib

theorem algebra_185843 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x^2 - y^2 = y * z) (h2 : y^2 - z^2 = x * z) :
    x^2 - z^2 = x * y := by
  have eq3 : x^2 - z^2 = z * (x + y) := by
    linarith
  have eq4 : z * (x + y) = x * y := by
    apply (mul_left_inj' (show y ≠ 0 by assumption)).mp
    have h3 : x^2 - y^2 = y * z := h1
    have h4 : y^2 - z^2 = x * z := h2
    field_simp [hy] at h3 h4 ⊢
    nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_pos_of_ne_zero hz,
      sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (x * z)
    ]
  have eq5 : x^2 - z^2 = x * y := by
    linarith [eq3, eq4]
  linarith [eq5]