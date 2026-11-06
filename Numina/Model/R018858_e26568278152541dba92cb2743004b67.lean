import Mathlib

theorem algebra_198830 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x^2 * y - 6 / (x * y) = 13) (h2 : x * y + x^2 * y = 6) :
    (x, y) = (-7, 1 / 7) ∨ (x, y) = (-2, 3) := by

  have eq3 : x^3 * y^2 - 13 * (x * y) - 6 = 0 := by
    have h1' : x * y ≠ 0 := mul_ne_zero hx hy
    have h3 : x^2 * y - 6 / (x * y) = 13 := h1
    have h4 : x * y ≠ 0 := h1'
    field_simp [h4] at h3
    nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_pos_of_ne_zero h4]

  have eq2 : x * y * (1 + x) = 6 := by 
    nlinarith
  have h3 : 1 + x ≠ 0 := by
    by_contra h
    have h4 : x = -1 := by linarith
    rw [h4] at eq2
    nlinarith
  have h4' : x * y = 6 / (1 + x) := by
    have h5 : 1 + x ≠ 0 := h3
    have eq2' : x * y * (1 + x) = 6 := eq2
    have h6 : x * y = 6 / (1 + x) := by
      field_simp [h5] at eq2' ⊢
      <;> nlinarith
    linarith
  have eq4 : (x + 7) * (x + 2) = 0 := by
    have eq5 : x^2 + 9 * x + 14 = 0 := by
      have eq3' : x^3 * y^2 - 13 * (x * y) - 6 = 0 := eq3
      have h4'' : x * y = 6 / (1 + x) := h4'
      have eq6 : x^2 + 9 * x + 14 = 0 := by
        have h5 : (1 + x) ≠ 0 := h3
        have eq7 : x^3 * y^2 = x * (x * y)^2 := by ring
        rw [eq7] at eq3'
        rw [show x * y = 6 / (1 + x) by linarith [h4'']] at eq3'
        field_simp [h5] at eq3' ⊢
        <;> nlinarith [sq_nonneg (x + 7), sq_nonneg (x + 2)]
      linarith
    nlinarith
  cases' (mul_eq_zero.mp eq4) with h6 h7
  · -- Case 1: x + 7 = 0, so x = -7
    have hx1 : x = -7 := by linarith
    have hy1 : y = 1 / 7 := by
      rw [hx1] at eq2
      nlinarith
    left
    simp [hx1, hy1]
  · -- Case 2: x + 2 = 0, so x = -2
    have hx1 : x = -2 := by linarith
    have hy1 : y = 3 := by
      rw [hx1] at eq2
      nlinarith
    right
    simp [hx1, hy1]