import Mathlib

theorem algebra_306463 {a b : ℝ} (ha : a ≠ b) (h1 : (a + 1)^2 = 3 - 3 * (a + 1)) (h2 : 3 * (b + 1) = 3 - (b + 1)^2) :
    b * Real.sqrt (b / a) + a * Real.sqrt (a / b) = -23 := by
  have ha2 : a ^ 2 + 5 * a + 1 = 0 := by
    nlinarith
  have hb2 : b ^ 2 + 5 * b + 1 = 0 := by 
    nlinarith
  have h_ne_a : a ≠ 0 := by 
    by_contra h 
    rw [h] at ha2 
    nlinarith 
  have h_ne_b : b ≠ 0 := by 
    by_contra h 
    rw [h] at hb2 
    nlinarith
  have hab1 : a + b = -5 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne ha), sq_pos_of_ne_zero (show b - a ≠ 0 by 
      intro h'
      apply ha
      linarith
    )]
  have hab2 : a * b = 1 := by 
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne ha), sq_pos_of_ne_zero (show b - a ≠ 0 by 
      intro h'
      apply ha
      linarith
    )]
  have h3 : b / a > 0 := by
    have ha3 : a < 0 := by
      nlinarith [sq_nonneg (a + 5 / 2), sq_nonneg (a * b), hab2]
    have hb3 : b < 0 := by
      nlinarith [sq_nonneg (b + 5 / 2), sq_nonneg (a * b), hab2]
    apply div_pos_of_neg_of_neg
    all_goals linarith 
  have h4 : a / b > 0 := by
    have ha3 : a < 0 := by
      nlinarith [sq_nonneg (a + 5 / 2), sq_nonneg (a * b), hab2]
    have hb3 : b < 0 := by
      nlinarith [sq_nonneg (b + 5 / 2), sq_nonneg (a * b), hab2]
    apply div_pos_of_neg_of_neg
    all_goals linarith 
  have h5 : b / a = b ^ 2 := by
    have h8 : a ≠ 0 := by 
      exact h_ne_a 
    have h9 : b / a = b * (1 / a) := by 
      field_simp 
    have h10 : 1 / a = b := by
      have h11 : a * b = 1 := hab2 
      have h12 : a ≠ 0 := h_ne_a 
      field_simp at h11 ⊢
      nlinarith 
    rw [h9, h10]
    all_goals ring 
  have h6 : a / b = a ^ 2 := by
    have h8 : b ≠ 0 := by 
      exact h_ne_b 
    have h9 : a / b = a * (1 / b) := by 
      field_simp 
    have h10 : 1 / b = a := by
      have h11 : a * b = 1 := hab2 
      have h12 : b ≠ 0 := h_ne_b 
      field_simp at h11 ⊢ 
      nlinarith 
    rw [h9, h10]
    all_goals ring 
  have h7 : b < (0 : ℝ) := by
    nlinarith [sq_nonneg (a + 5 / 2), sq_nonneg (b + 5 / 2), sq_nonneg (a * b), hab2]
  have h8 : a < (0 : ℝ) := by
    nlinarith [sq_nonneg (a + 5 / 2), sq_nonneg (b + 5 / 2), sq_nonneg (a * b), hab2]
  have h9 : Real.sqrt (b / a) = -b := by
    rw [show b / a = b ^ 2 by linarith [h5]]
    have h10 : Real.sqrt (b ^ 2) = -b := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_neg (show b < 0 by linarith [h7] ) ]
      all_goals nlinarith
    linarith [h10] 
  have h10 : Real.sqrt (a / b) = -a := by
    rw [show a / b = a ^ 2 by linarith [h6]]
    have h11 : Real.sqrt (a ^ 2) = -a := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_neg (show a < 0 by linarith [h8] ) ]
      all_goals nlinarith 
    linarith [h11] 
  have h11 : b * Real.sqrt (b / a) + a * Real.sqrt (a / b) = - (a ^ 2 + b ^ 2) := by
    rw [h9, h10]
    all_goals nlinarith
  have h12 : a ^ 2 + b ^ 2 = 23 := by
    nlinarith [ha2, hb2, hab1, hab2] 
  linarith [h11, h12]