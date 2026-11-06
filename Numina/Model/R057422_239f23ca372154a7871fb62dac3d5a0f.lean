import Mathlib

theorem algebra_310950 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1995) :
    3 * Real.sqrt 665 ≤ a * b / c + b * c / a + c * a / b := by 

  have h1 : 0 < a * b / c := by
    apply div_pos
    nlinarith
    linarith
  have h2 : 0 < b * c / a := by
    apply div_pos
    nlinarith
    linarith
  have h3 : 0 < c * a / b := by
    apply div_pos
    nlinarith
    linarith
  have h4 : a * b / c + b * c / a + c * a / b - 3 * Real.sqrt 665 ≥ 0 := by
    have h5 : Real.sqrt 665 ^ 2 = 665 := by
      rw [Real.sq_sqrt]
      norm_num
    have h6 : Real.sqrt 665 ≥ 0 := Real.sqrt_nonneg 665
    have h9 : a * b * c > 0 := by
      apply mul_pos
      apply mul_pos
      exact ha
      exact hb
      exact hc
    have h10 : a * b / c + b * c / a + c * a / b - 3 * Real.sqrt 665 ≥ 0 := by
      have h12 : (a * b / c + b * c / a + c * a / b - 3 * Real.sqrt 665) =
          (a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - 3 * Real.sqrt 665 * (a * b * c)) / (a * b * c) := by
        field_simp
        ring
      rw [h12]
      have h13 : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - 3 * Real.sqrt 665 * (a * b * c) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a * b - Real.sqrt 665 * c), sq_nonneg (b * c - Real.sqrt 665 * a), sq_nonneg (c * a - Real.sqrt 665 * b),
          Real.sqrt_nonneg 665, Real.sq_sqrt (show (0 : ℝ) ≤ 665 by norm_num), 
          h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith