import Mathlib

theorem algebra_325944 {a b : ℝ} (ha : a^2 + 11 * a = -16) (hb : b^2 + 11 * b = -16)
    (hab : a ≠ b) :
    Real.sqrt (b / a) + Real.sqrt (a / b) = 11 / 4 := by
  have h1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    nlinarith
  have h2 : b ≠ 0 := by
    by_contra h
    rw [h] at hb
    nlinarith
  have h3 : a + b = -11 := by
    have ha' : a^2 + 11 * a + 16 = 0 := by linarith
    have hb' : b^2 + 11 * b + 16 = 0 := by linarith
    have eq1 : a^2 - b^2 + 11 * (a - b) = 0 := by
      linarith [ha', hb']
    have eq2 : (a - b) * (a + b + 11) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq2) with h4 h5
    · -- Case where a - b = 0
      exfalso
      exact hab (by linarith)
    · -- Case where a + b + 11 = 0
      linarith
  have h4 : a * b = 16 := by
    have ha' : a^2 + 11 * a + 16 = 0 := by linarith
    have hb' : b^2 + 11 * b + 16 = 0 := by linarith
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply hab
      linarith
    ), sq_nonneg (a - b), sq_nonneg (a + b)]
  have h5 : b / a + a / b = 89 / 16 := by
    have h6 : a ≠ 0 := h1
    have h7 : b ≠ 0 := h2
    field_simp [h6, h7]
    nlinarith [h3, h4]
  have h6 : Real.sqrt (b / a) + Real.sqrt (a / b) ≥ 0 := by
    apply add_nonneg
    · -- Real.sqrt (b / a) ≥ 0
      apply Real.sqrt_nonneg
    · -- Real.sqrt (a / b) ≥ 0
      apply Real.sqrt_nonneg
  have h9 : a * b = 16 := h4
  have h10 : b / a ≥ 0 := by
    have ha1 : a ≠ 0 := h1
    have hb1 : b ≠ 0 := h2
    have hsq : a * b = 16 := h4
    have h10 : b / a ≥ 0 := by
      have h11 : a ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        exact h1
      have h111 : b / a = 16 / (a ^ 2) := by
        field_simp [h1, h2]
        <;> nlinarith [h9]
      rw [h111]
      apply div_nonneg
      norm_num
      linarith
    linarith
  have h10' : a / b ≥ 0 := by
    have ha1 : a ≠ 0 := h1
    have hb1 : b ≠ 0 := h2
    have hsq : a * b = 16 := h4
    have h100 : a / b ≥ 0 := by
      have h101 : a / b = 16 / (b ^ 2) := by
        field_simp [h1, h2]
        <;> nlinarith [h9]
      rw [h101]
      apply div_nonneg
      norm_num
      have h7b : b ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        exact h2
      linarith
    linarith
  have h7 : (Real.sqrt (b / a) + Real.sqrt (a / b))^2 = 121 / 16 := by
    have h8 : (Real.sqrt (b / a) + Real.sqrt (a / b))^2 =
      (Real.sqrt (b / a))^2 + (Real.sqrt (a / b))^2 + 2 * (Real.sqrt (b / a) * Real.sqrt (a / b)) := by ring
    have h9 : (Real.sqrt (b / a))^2 = b / a := Real.sq_sqrt h10
    have h10' : (Real.sqrt (a / b))^2 = a / b := Real.sq_sqrt h10'
    have h11 : Real.sqrt (b / a) * Real.sqrt (a / b) = 1 := by
      have h12 : Real.sqrt (b / a) * Real.sqrt (a / b) = Real.sqrt ((b / a) * (a / b)) := by
        rw [← Real.sqrt_mul (by
          all_goals
            nlinarith [h10, h10']
        )]
      rw [h12]
      have h16 : (b / a) * (a / b) = 1 := by
        have ha17 : a ≠ 0 := h1
        have hb17 : b ≠ 0 := h2
        field_simp [ha17, hb17]
      rw [h16]
      all_goals
        norm_num [Real.sqrt_eq_iff_sq_eq]
    nlinarith
  have h7' : Real.sqrt (b / a) + Real.sqrt (a / b) = 11 / 4 := by
    nlinarith [h7, h6, Real.sqrt_nonneg (b / a), Real.sqrt_nonneg (a / b)]
  exact h7'