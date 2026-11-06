import Mathlib

theorem algebra_3278 {x k : ℝ} (hx1 : x^2 - 3 * x + 1 = 0) (hx2 : x ≠ 0) (h : 1 / x^4 - 7 / x^2 = k) : k = -1 := by
  have h1 : x^2 = 3 * x - 1 := by
    linarith
  have h2 : x + 1 / x = 3 := by
    field_simp [hx2]
    nlinarith
  have h3 : 1 / x^2 = 8 - 3 * x := by
    have hx5 : 1 / x = 3 - x := by
      field_simp [hx2]
      nlinarith
    -- use field_simp
    calc
      1 / x^2 = (1 / x) ^ 2 := by ring_nf
      _ = (3 - x) ^ 2 := by rw [hx5]
      _ = 8 - 3 * x := by
        nlinarith [h1]
  have h4 : 1 / x^4 = 55 - 21 * x := by
    calc
      1 / x^4 = (1 / x^2)^2 := by ring_nf
      _ = (8 - 3 * x) ^ 2 := by rw [h3]
      _ = 55 - 21 * x := by
        have hx2' : x^2 = 3 * x - 1 := h1
        nlinarith [sq_nonneg (x - 3)]
  -- Now compute the expression
  have h5 : 1 / x^4 - 7 / x^2 = -1 := by
    have eq1 : 1 / x^4 = 55 - 21 * x := h4
    have eq2 : 1 / x^2 = 8 - 3 * x := h3
    -- need to rewrite
    have eq3 : 7 / x^2 = 7 * (8 - 3 * x) := by
      rw [show 7 / x^2 = 7 * (1 / x^2) by ring]
      rw [eq2]
      all_goals nlinarith
    -- need to compute
    have eq4 : 1 / x^4 - 7 / x^2 = (55 - 21 * x) - 7 * (8 - 3 * x) := by
      rw [show 1 / x^4 - 7 / x^2 = (1 / x^4) - 7 / x^2 by rfl]
      rw [eq1, eq3]
      all_goals nlinarith
    nlinarith [eq4]
  -- Now for the final step
  linarith [h, h5]