import Mathlib

theorem algebra_248005 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    1 < a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) ∧
    a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by
  constructor
  · -- Show that sum is greater than 1
    have h1 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) > 1 := by
      have h2 : 0 < (a + b + c) * (a + b + d) * (b + c + d) * (a + c + d) := by positivity
      have h3 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 > 0 := by
        have h6 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 =
            (a * (a + b + c) * (b + c + d) * (a + c + d) + b * (a + b + d) * (b + c + d) * (a + c + d) + c * (a + b + d) * (a + b + c) * (a + c + d) + d * (a + b + d) * (a + b + c) * (b + c + d) - (a + b + c) * (a + b + d) * (b + c + d) * (a + c + d)) / ((a + b + c) * (a + b + d) * (b + c + d) * (a + c + d)) := by 
          field_simp
          ring
        rw [h6]
        apply div_pos
        · -- Show that numerator is positive 
          nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos hd, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
        all_goals positivity
      linarith
    linarith
  · -- Show that sum is less than 2
    have h12 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 2 < 0 := by
      have h14 : 0 < (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) := by positivity
      have h15 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 2 =
          (a * (a + b + c) * (b + c + d) * (a + c + d) + 
           b * (a + b + d) * (b + c + d) * (a + c + d) + 
           c * (a + b + d) * (a + b + c) * (a + c + d) + 
           d * (a + b + d) * (a + b + c) * (b + c + d) - 
           2 * (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) / ((a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) := by 
        field_simp
        ring 
      rw [h15]
      apply div_neg_of_neg_of_pos
      · -- Show numerator is negative 
        nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos hd, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
      · -- Show denominator is positive 
        positivity
    linarith [h12]