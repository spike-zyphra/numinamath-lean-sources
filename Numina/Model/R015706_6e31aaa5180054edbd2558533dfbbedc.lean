import Mathlib

theorem algebra_325637 {a b : ℝ} (ha : a ≠ b) (h1 : (a + 1)^2 = 3 - 3 * (a + 1)) (h2 : 3 * (b + 1) = 3 - (b + 1)^2) :
    b * Real.sqrt (b / a) + a * Real.sqrt (a / b) = -23 := by

  have h3 : (a + 1) ^ 2 + 3 * (a + 1) - 3 = 0 := by
    nlinarith

  have h4 : (b + 1) ^ 2 + 3 * (b + 1) - 3 = 0 := by
    nlinarith

  have h5 : (a - b) * (a + b + 5) = 0 := by
    nlinarith [h3, h4]

  have h6 : a + b + 5 = 0 := by
    apply (mul_left_inj' (show a - b ≠ 0 by intro h; apply ha; linarith)).mp
    linarith

  have h7 : a + b = -5 := by linarith

  have h8 : a * b = 1 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by intro h; apply ha; linarith), h3, h4, h7]

  have ha0 : a ≠ 0 := by
    by_contra h
    have h9 : a * b = 0 := by
      rw [h]
      norm_num
    nlinarith [h8, h9]

  have hb0 : b ≠ 0 := by
    by_contra h
    have h9 : a * b = 0 := by
      rw [h]
      norm_num
    nlinarith [h8, h9]

  have h10 : a < 0 := by
    nlinarith [sq_nonneg (a + 2.5), sq_nonneg (b + 2.5), h7, h8, mul_self_nonneg (a), mul_self_nonneg (b)]

  have h11 : b < 0 := by
    nlinarith [sq_nonneg (a + 2.5), sq_nonneg (b + 2.5), h7, h8, mul_self_nonneg (a), mul_self_nonneg (b)]

  have h15 : Real.sqrt (b / a) = - b := by
    have h16 : b / a = b ^ 2 := by
      have h17 : a * b = 1 := h8
      have h18 : a = 1 / b := by
        field_simp [hb0]
        all_goals nlinarith
      rw [h18]
      field_simp [hb0]
      <;> nlinarith
    rw [h16]
    have h17 : Real.sqrt (b ^ 2) = - b := by
      rw [Real.sqrt_sq_eq_abs]
      have h18 : b < 0 := h11
      have h19 : |b| = -b := abs_of_neg h18
      linarith
    exact h17

  have h16 : Real.sqrt (a / b) = - a := by
    have h17 : a / b = a ^ 2 := by
      have h18 : a * b = 1 := h8
      have h19 : b = 1 / a := by
        field_simp [ha0]
        all_goals nlinarith
      rw [h19]
      field_simp [ha0]
      <;> nlinarith
    rw [h17]
    have h18 : Real.sqrt (a ^ 2) = - a := by
      rw [Real.sqrt_sq_eq_abs]
      have h19 : a < 0 := h10
      have h20 : |a| = -a := abs_of_neg h19
      linarith
    exact h18

  rw [h15, h16]

  have h17 : a ^ 2 + b ^ 2 = 23 := by
    nlinarith [h7, h8, sq_pos_of_ne_zero (show a - b ≠ 0 by intro h; apply ha; linarith)]

  nlinarith [h17, h10, h11]