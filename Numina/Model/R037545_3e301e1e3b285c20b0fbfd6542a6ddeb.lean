import Mathlib


theorem algebra_246429 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ((a / b - b / a) / ((a + b) * (1 / b - 1 / a)) - a / b) / (a / b + 1) = 1 / 2014) :
    a / b = 2013 / 2015 := by

  have h1 : a + b ≠ 0 := by
    by_contra h1
    have h2 : a = -b := by linarith
    have h3 : a / b + 1 = 0 := by
      rw [show a = -b by linarith]
      field_simp [hb]
    rw [h3] at h
    norm_num [h3] at h

  have h2 : a - b ≠ 0 := by
    by_contra h2
    have h3 : a = b := by linarith
    have h4 : a / b = 1 := by
      rw [show b = a by linarith [h3]]
      field_simp [ha]
    -- Now substitute into the original expression.
    -- If a = b, then (a / b - b / a) / ((a + b) * (1 / b - 1 / a)) = (1 - 1) / ((a + a) * (1 / a - 1 / a)) = 0 / (0) which is division by zero.
    have h8 : (a / b - b / a) / ((a + b) * (1 / b - 1 / a)) = 0 := by
      rw [show a = b by linarith [h3]]
      field_simp [hb]
      all_goals
        nlinarith
    have h6 : ((a / b - b / a) / ((a + b) * (1 / b - 1 / a)) - a / b) / (a / b + 1) = (0 - 1) / 2 := by
      rw [h8, h4]
      all_goals
        norm_num
    rw [h6] at h
    norm_num at h

  have eq1 : (a / b - b / a) / ((a + b) * (1 / b - 1 / a)) = 1 := by
    have h11 : a + b ≠ 0 := h1
    have h12 : a - b ≠ 0 := h2
    have h3 : a * b ≠ 0 := by
      apply mul_ne_zero
      exact ha
      exact hb
    field_simp [hb, ha, show a + b ≠ 0 by exact h1, show a - b ≠ 0 by exact h2]
    have h4 : (a ^ 2 - b ^ 2 : ℝ) = (a + b) * (a - b) := by
      ring
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero (show (a + b) ≠ 0 by exact h1), sq_pos_of_ne_zero (show (a - b) ≠ 0 by exact h2)]

  have h3 : ((a / b - b / a) / ((a + b) * (1 / b - 1 / a)) - a / b) / (a / b + 1) = (b - a) / (a + b) := by
    have eq1' : (a / b - b / a) / ((a + b) * (1 / b - 1 / a)) = 1 := eq1
    have h3 : a / b + 1 ≠ 0 := by
      by_contra h4
      have h4' : a / b = -1 := by linarith
      have h5 : a = -b := by
        have h7 : a / b = -1 := h4'
        have : a = -b := by
          field_simp [hb] at h7 ⊢
          nlinarith
        linarith
      have h7 : a + b = 0 := by linarith [h5]
      contradiction
    field_simp [hb, ha, show a + b ≠ 0 by exact h1, show a - b ≠ 0 by exact h2, h3]
    <;> nlinarith

  rw [h3] at h

  have h4 : 2014 * (b - a) = a + b := by
    have h5 : a + b ≠ 0 := h1
    field_simp [show a + b ≠ 0 by exact h1] at h ⊢
    nlinarith

  have h5 : 2013 * b = 2015 * a := by
    nlinarith

  have h6 : a / b = 2013 / 2015 := by
    have hb' : b ≠ 0 := hb
    field_simp [hb']
    nlinarith

  linarith