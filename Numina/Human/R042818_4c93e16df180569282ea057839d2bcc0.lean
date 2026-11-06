import Mathlib

/- solve the equation : x^3/y + xy = 40, y^3/x + xy = 10-/
theorem algebra_166367 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x^3 / y + x * y = 40) (h2 : y^3 / x + x * y = 10) :
    (x, y) = (4, 2) ∨ (x, y) = (-4, -2) := by
  have h1' : x^3 + x * y^2 = 40 * y := by
    have h : x^3 / y + x * y = 40 := h1
    have h_mul_y : (x^3 / y) * y + (x * y) * y = 40 * y := by
      field_simp [hy] at h ⊢
      linarith
    have eq1 : (x^3 / y) * y = x^3 := by
      field_simp [hy]
    have eq2 : (x * y) * y = x * y^2 := by
      ring
    rw [eq1, eq2] at h_mul_y
    linarith

  have h2' : y^3 + x^2 * y = 10 * x := by
    have h : y^3 / x + x * y = 10 := h2
    have h_mul_x : (y^3 / x) * x + (x * y) * x = 10 * x := by
      field_simp [hx] at h ⊢
      linarith
    have eq1 : (y^3 / x) * x = y^3 := by
      field_simp [hx]
    have eq2 : (x * y) * x = x^2 * y := by
      ring
    rw [eq1, eq2] at h_mul_x
    linarith

  have h3 : x^2 + y^2 = 20 := by
    have eq1 : (x^3 / y + x * y) * (y^3 / x + x * y) = 400 := by
      rw [h1, h2]
      norm_num
    have eq2 : (x^3 / y + x * y) * (y^3 / x + x * y) = (x^2 + y^2) ^ 2 := by
      field_simp [hx, hy]
      nlinarith [sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y)]
    have h4 : (x^2 + y^2) ^ 2 = 400 := by
      nlinarith [eq1, eq2]
    have h5 : x^2 + y^2 ≥ 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    have h6 : x^2 + y^2 = 20 := by
      nlinarith [h4, h5]
    exact h6

  have h4 : x = 2 * y := by
    have eq1 : (x - y) * (x^2 + y^2) = 10 * (4 * y - x) := by
      nlinarith [h1', h2', h3]
    rw [h3] at eq1
    have eq2 : 20 * (x - y) = 10 * (4 * y - x) := by linarith
    nlinarith

  have hy2 : y^2 = 4 := by
    have h4' : x = 2 * y := h4
    rw [h4'] at h3
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]

  have hy_eq : y = 2 ∨ y = -2 := by
    have h : y^2 = 4 := hy2
    have h1 : y = 2 ∨ y = -2 := by
      have h_eq : y^2 - 4 = 0 := by linarith
      have h_factored : (y - 2) * (y + 2) = 0 := by
        rw [←h_eq]
        ring
      cases (mul_eq_zero.mp h_factored) with
      | inl h2 => 
        left
        linarith
      | inr h3 => 
        right
        linarith
    exact h1
  
  cases hy_eq with
  | inl hy2 =>
    have hx2 : x = 4 := by
      rw [hy2] at h4
      linarith
    left
    exact Prod.ext hx2 hy2
  | inr hy2 =>
    have hx2 : x = -4 := by
      rw [hy2] at h4
      linarith
    right
    exact Prod.ext hx2 hy2