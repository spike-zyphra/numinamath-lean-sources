import Mathlib

theorem inequalities_43472 (x y a b : ℝ) (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) (hb : 0 < b)
    (hxy : x ≠ y) (hx2y : x ≠ 2 * y) (hy2x : y ≠ 2 * x) (a3b : a ≠ 3 * b)
    (h : (2 * x - y) / (2 * y - x) = (a + 3 * b) / (a - 3 * b)) :
    (x ^ 2 + y ^ 2) / (x ^ 2 - y ^ 2) ≥ 1 := by

  have h1 : 2 * y - x ≠ 0 := by
    intro h2
    apply hx2y
    linarith

  have h2 : a - 3 * b ≠ 0 := by
    intro h3
    apply a3b
    linarith

  have h3 : (2 * x - y) * (a - 3 * b) = (a + 3 * b) * (2 * y - x) := by
    have h1' : 2 * y - x ≠ 0 := h1
    have h2' : a - 3 * b ≠ 0 := h2
    field_simp [h1', h2'] at h ⊢
    linarith

  have h4 : x * (a - b) = y * (a + b) := by
    nlinarith

  have h5 : a - b > 0 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_ne_zero (sub_ne_zero_of_ne a3b)]

  have h6 : x > y := by
    have h5' : a - b > 0 := h5
    have h7 : x * (a - b) = y * (a + b) := h4
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]

  have h7 : x ^ 2 - y ^ 2 > 0 := by
    nlinarith [h6, mul_pos hx hy]

  have h8 : (x ^ 2 + y ^ 2) / (x ^ 2 - y ^ 2) - 1 ≥ 0 := by
    have h9 : x ^ 2 - y ^ 2 > 0 := h7
    have h10 : (x ^ 2 + y ^ 2) / (x ^ 2 - y ^ 2) - 1 =
        (2 * y ^ 2) / (x ^ 2 - y ^ 2) := by
      field_simp [h9]
      nlinarith
    rw [h10]
    apply div_nonneg
    nlinarith [sq_pos_of_pos hy]
    nlinarith

  linarith