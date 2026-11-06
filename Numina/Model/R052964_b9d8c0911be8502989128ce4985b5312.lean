import Mathlib

theorem algebra_322363 {a b : ℝ} (ha : a < b) (hb : b < 0) (h : a^2 + b^2 = 4 * a * b) :
    (a + b) / (a - b) = Real.sqrt 3 := by
  have h1 : a < 0 := by linarith
  have h2 : a - b < 0 := by linarith
  have h3 : (a + b) ^ 2 = 6 * a * b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have h4 : (a - b) ^ 2 = 2 * a * b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  -- $(a + b)^2 / (a - b)^2 = 3$ so $(\frac{a + b}{a - b})^2 = 3$
  have h5 : ((a + b) / (a - b)) ^ 2 = 3 := by
    have h6 : a - b ≠ 0 := by linarith
    field_simp [h6]
    -- Now we have (a + b)^2 / (a - b)^2
    -- Let's compute (a + b)^2 and (a - b)^2
    -- (a + b)^2 = a^2 + 2ab + b^2 and (a - b)^2 = a^2 - 2ab + b^2
    -- We have from h: a^2 + b^2 = 4ab
    -- Then (a + b)^2 = (a^2 + b^2) + 2ab = 4ab + 2ab = 6ab
    -- Similarly (a - b)^2 = (a^2 + b^2) - 2ab = 4ab - 2ab = 2ab
    nlinarith [h3, h4]
  -- $\frac{a + b}{a - b} > 0$ because both numerator and denominator are negative
  have h6 : (a + b) / (a - b) > 0 := by
    apply div_pos_of_neg_of_neg
    · -- Show that a + b < 0
      nlinarith
    · -- Show that a - b < 0
      linarith
  have h7 : Real.sqrt 3 > 0 := by positivity
  have h8 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  have h9 : (a + b) / (a - b) = Real.sqrt 3 := by
    have h10 : ((a + b) / (a - b)) ^ 2 = (Real.sqrt 3) ^ 2 := by
      rw [h5, h8]
    have h11 : (a + b) / (a - b) = Real.sqrt 3 := by
      nlinarith [h10, h6, Real.sqrt_nonneg 3]
    exact h11
  exact h9