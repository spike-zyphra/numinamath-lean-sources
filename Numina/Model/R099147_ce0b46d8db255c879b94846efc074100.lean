import Mathlib

theorem algebra_100029 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : 1/x - 1/(2*y) = 1/(2*x + y)) :
    y^2/x^2 + x^2/y^2 = 9/4 := by
  have h1 : 2 * x + y ≠ 0 := by
    by_contra h2
    have h3 : 1/(2*x + y) = 0 := by
      rw [h2]
      norm_num
    have h4 : 1/x - 1/(2*y) = 0 := by
      linarith [h, h3]
    have h5 : 1/x = 1/(2*y) := by
      linarith
    have h6 : 2 * y = x := by
      field_simp [hx, hy] at h5
      linarith
    have h7 : y = 0 := by
      nlinarith [h2, h6]
    contradiction

  field_simp [hx, hy, h1] at h

  have h2 : 2 * x^2 - x * y - 2 * y^2 = 0 := by
    nlinarith

  have eq2 : y^2 / x^2 + x^2 / y^2 = (y^4 + x^4) / (x^2 * y^2) := by
    field_simp [hx, hy]
    <;> ring

  have eq4 : y^4 + x^4 = 9 / 4 * (x^2 * y^2) := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - 2 * y), sq_nonneg (2 * x - y)]

  rw [eq2]
  field_simp [hx, hy]
  nlinarith [eq4, h2]