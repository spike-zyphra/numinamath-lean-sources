import Mathlib

theorem algebra_172823 {x y : ℝ}  (hx : x^2 ≠ 0) (hy : y^2 ≠ 0)  (hxy : x ≠ y)  (h : 1 / (1 + x^2) + 1 / (1 + y^2) = 2 / (1 + x * y)) :  x * y = 1   := by
  have hx2 : 1 + x^2 ≠ 0 := by
    by_contra h1
    have h2 : x^2 ≥ 0 := sq_nonneg x
    nlinarith
  have hy2 : 1 + y^2 ≠ 0 := by
    by_contra h1
    have h2 : y^2 ≥ 0 := sq_nonneg y
    nlinarith
  have h1 : 1 + x * y ≠ 0 := by
    by_contra h1
    have eq : 1 / (1 + x^2) + 1 / (1 + y^2) = 2 / (1 + x * y) := h
    rw [show 1 + x * y = (0 : ℝ) by linarith] at h
    field_simp [hx2, hy2] at h
    <;> nlinarith [sq_nonneg (x * y), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - 1)]
  have eq1 : (1 + y^2) * (1 + x * y) + (1 + x^2) * (1 + x * y) = 2 * (1 + x^2) * (1 + y^2) := by
    field_simp [hx2, hy2, h1] at h ⊢
    nlinarith
  have eq2 : x * y = 1 := by
    have h2 : (x * y - 1) ^ 2 = 0 := by
      nlinarith [sq_pos_of_ne_zero (show 1 + x * y ≠ 0 by assumption), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_pos_of_ne_zero (show (x - y) ^ 2 ≠ 0 by
        by_contra h'
        have h_eq : x = y := by
          nlinarith
        contradiction
      )]
    have h3 : x * y - 1 = 0 := by
      rw [sq_eq_zero_iff] at h2
      linarith
    linarith
  exact eq2