import Mathlib

theorem algebra_280286 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a + b^2 / a = b + a^2 / b) : a = b := by
  have eq1 : a + b^2 / a = b + a^2 / b := h
  have eq2 : a * b * (a + b ^ 2 / a) = a * b * (b + a ^ 2 / b) := by
    rw [eq1]
  have eq3 : a * b * (a + b ^ 2 / a) = a ^ 2 * b + b ^ 3 := by
    field_simp [ha]
    all_goals ring
  have eq4 : a * b * (b + a ^ 2 / b) = a * b ^ 2 + a ^ 3 := by
    field_simp [hb]
    all_goals ring
  rw [eq3] at eq2
  rw [eq4] at eq2
  -- The equation becomes: $a^2 * b + b^3 = a * b^2 + a^3$
  -- Rearranging terms: $a^2 * b + b^3 - a * b^2 - a^3 = 0$
  -- Factor: $(a - b)(-a^2 - b^2) = 0$
  have eq5 : a ^ 2 * b + b ^ 3 - (a * b ^ 2 + a ^ 3) = 0 := by linarith
  have eq6 : (a - b) * (-a^2 - b ^ 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq6) with h7 h8
  · -- Case $a - b = 0$
    linarith
  · -- Case $-a^2 - b^2 = 0$
    have h9 : a^2 + b^2 = 0 := by
      nlinarith
    have ha2 : a^2 ≥ 0 := sq_nonneg a
    have hb2 : b^2 ≥ 0 := sq_nonneg b
    have ha2' : a^2 = 0 := by linarith [h9, ha2, hb2]
    have hb2' : b^2 = 0 := by linarith [h9, ha2, hb2]
    have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    contradiction