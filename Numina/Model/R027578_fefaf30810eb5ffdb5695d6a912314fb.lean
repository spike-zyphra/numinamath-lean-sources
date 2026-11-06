import Mathlib

theorem algebra_1460 {a b : ℝ} (hab : a * b ≠ 1) (ha : 2 * a ^ 2 + 1234567890 * a + 3 = 0)
    (hb : 3 * b ^ 2 + 1234567890 * b + 2 = 0) : a / b = 3 / 2 := by
  have h1 : b ≠ 0 := by
    by_contra h
    rw [h] at hb
    nlinarith
  have h2 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    nlinarith
  have h3 : 2 * a ^ 2 + 3 = -1234567890 * a := by linarith
  have h4 : 3 * b ^ 2 + 2 = -1234567890 * b := by linarith
  have h8 : (a * b - 1) * (2 * a - 3 * b) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact h2), sq_pos_of_ne_zero (show b ≠ 0 by exact h1), sq_nonneg (a - b), sq_nonneg (a * b - 1)]
  cases' (mul_eq_zero.1 h8) with h9 h10
  · -- If a * b - 1 = 0, then a * b = 1, which contradicts the hypothesis
    exfalso
    have h11 : a * b = 1 := by linarith
    tauto
  · -- If 2 * a - 3 * b = 0, then 2 * a = 3 * b
    have h12 : 2 * a = 3 * b := by linarith
    have h16 : a / b = 3 / 2 := by
      have h18 : 2 * a = 3 * b := h12 
      have h19 : b ≠ 0 := h1
      have h20 : a / b = 3 / 2 := by
        have h22 : a = (3 / 2) * b := by 
          linarith 
        rw [h22]
        field_simp [h19]
        <;> linarith
      linarith
    exact h16