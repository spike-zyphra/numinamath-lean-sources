import Mathlib

theorem algebra_21819 (h k a b : ℝ) (ha : a > 0) (hb : b > 0)
    (h1 : ∀ x y, (9 * x ^ 2 + 4 * y ^ 2 - 54 * x + 40 * y + 145 = 0) ↔
      ((x - h) ^ 2 / a ^ 2 + (y - k) ^ 2 / b ^ 2 = 1)) :
    h + k + a + b = 3 := by
  have eq1 := h1 3 (-2)
  norm_num at eq1
  have eq2 := h1 3 (-8)
  norm_num at eq2
  have eq3 := h1 5 (-5)
  norm_num at eq3
  have eq4 := h1 1 (-5)
  norm_num at eq4
  have hk1 : k = -5 := by
    have eq5 : ((-2 - k) ^ 2) / b ^ 2 = ((-8 - k) ^ 2) / b ^ 2 := by
      have h2 : ((3 - h) ^ 2 / a ^ 2 + (-2 - k) ^ 2 / b ^ 2) = ((3 - h) ^ 2 / a ^ 2 + (-8 - k) ^ 2 / b ^ 2) := by
        linarith [eq1, eq2]
      linarith
    have hk2 : (-2 - k) ^ 2 = (-8 - k) ^ 2 := by
      have hb2 : b ^ 2 ≠ 0 := by
        nlinarith
      field_simp at eq5
      nlinarith
    nlinarith
  have ha1 : h = 3 := by
    rw [show k = -5 by linarith [hk1]] at eq3 eq4
    have h_eq1 : (5 - h) ^ 2 = a ^ 2 := by
      field_simp at eq3
      nlinarith
    have h_eq2 : (1 - h) ^ 2 = a ^ 2 := by
      field_simp at eq4
      nlinarith
    have h_eq3 : (5 - h) ^ 2 = (1 - h) ^ 2 := by
      linarith
    nlinarith
  have ha2 : a = 2 := by
    rw [show k = -5 by linarith [hk1]] at eq3
    rw [show h = 3 by linarith [ha1]] at eq3
    have h_eq1 : (5 - (3 : ℝ)) ^ 2 = a ^ 2 := by
      field_simp at eq3
      nlinarith
    nlinarith [sq_nonneg (a - 2)]
  have hb2 : b = 3 := by
    rw [show h = 3 by linarith [ha1], show k = -5 by linarith [hk1], show a = 2 by linarith [ha2]] at eq1
    field_simp at eq1
    nlinarith [sq_nonneg (b - 3)]
  linarith [ha1, hk1, ha2, hb2]