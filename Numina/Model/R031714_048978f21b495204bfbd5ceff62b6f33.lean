import Mathlib

theorem algebra_132609 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a + b + c = 0) (h2 : a / b + b / c + c / a = 100) :
    b / a + c / b + a / c = -103 := by
  have h3 : c = -a - b := by
    linarith
  have eq1 : a ^ 2 * c + b ^ 2 * a + c ^ 2 * b = 100 * (a * b * c) := by
    have eq2 : a / b + b / c + c / a = 100 := h2
    have eq3 : a / b + b / c + c / a = (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) / (a * b * c) := by
      field_simp [ha, hb, hc]
      ring
    rw [eq3] at eq2
    field_simp [ha, hb, hc] at eq2 ⊢
    linarith
  have eq5 : b / a + c / b + a / c = (b ^ 2 * c + a * c ^ 2 + a ^ 2 * b) / (a * b * c) := by
    field_simp [ha, hb, hc]
    ring
  rw [eq5]
  rw [show c = -a - b by linarith [h1]]
  have eq7 : a ^ 2 * (-a - b) + b ^ 2 * a + (-a - b) ^ 2 * b = 100 * (a * b * (-a - b)) := by
    rw [show c = -a - b by linarith [h1]] at eq1
    linarith
  field_simp [ha, hb, show (-a - b) ≠ 0 by
    intro h
    have h3 : c = 0 := by
      linarith [h1, h]
    contradiction
  ] at eq7 ⊢
  <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a * (b)), sq_nonneg ((-a - b)), sq_nonneg (b * (-a - b)), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero (show (-a - b) ≠ 0 by
    intro h
    have h3 : c = 0 := by
      linarith [h1, h]
    contradiction
  )]