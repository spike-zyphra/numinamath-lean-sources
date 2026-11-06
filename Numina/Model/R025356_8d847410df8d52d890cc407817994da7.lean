import Mathlib

theorem algebra_328254 {a b : ℝ} (ha : a ≠ b)
    (h1 : (a + 1)^2 = 3 - 3 * (a + 1)) (h2 : 3 * (b + 1) = 3 - (b + 1)^2) :
    b * Real.sqrt (b / a) + a * Real.sqrt (a / b) = -23 := by

  have h3 : a^2 + 5 * a + 1 = 0 := by
    nlinarith

  have h4 : b^2 + 5 * b + 1 = 0 := by
    nlinarith

  have h5 : a + b = -5 := by
    have h6 : a^2 - b^2 + 5 * (a - b) = 0 := by
      nlinarith [h3, h4]
    have h8 : a - b ≠ 0 := by
      intro h
      apply ha
      linarith
    have h9 : a + b = -5 := by
      apply (mul_left_inj' (show a - b ≠ 0 by
        exact h8
      )).mp
      nlinarith
    exact h9

  have h6 : a * b = 1 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply ha
      linarith
    ), h5]

  have h7 : b / a = b ^ 2 := by
    have h6' : a * b = 1 := h6
    have h6'' : a ≠ 0 := by
      by_contra h
      have : a * b = 0 := by
        rw [h]
        norm_num
      linarith [h6]
    field_simp [h6'']
    nlinarith

  have h8 : (a / b) = a ^ 2 := by
    have h6' : a * b = 1 := h6
    have h6'' : b ≠ 0 := by
      by_contra h
      have : a * b = 0 := by
        rw [h]
        norm_num
      linarith [h6]
    field_simp [h6'']
    nlinarith

  have h9 : b < 0 := by
    nlinarith [sq_nonneg (a + 5 / 2), sq_nonneg (b + 5 / 2), h5, h6, sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply ha
      linarith
    )]

  have h14 : a < 0 := by
    nlinarith [sq_nonneg (a + 5 / 2), sq_nonneg (b + 5 / 2), h5, h6, sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply ha
      linarith
    )]

  have h10 : Real.sqrt (b / a) = abs b := by
    rw [h7]
    have h11 : Real.sqrt (b ^ 2) = abs b := by
      rw [Real.sqrt_sq_eq_abs]
    exact h11

  have h12 : Real.sqrt (a / b) = abs a := by
    rw [h8]
    have h13 : Real.sqrt (a ^ 2) = abs a := by
      rw [Real.sqrt_sq_eq_abs]
    exact h13

  rw [h10, h12]

  have h16 : abs b = -b := by
    apply abs_of_neg
    linarith

  have h17 : abs a = -a := by
    apply abs_of_neg
    linarith

  rw [h16, h17]

  nlinarith [h5, h3, h4, sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply ha
      linarith
  )]