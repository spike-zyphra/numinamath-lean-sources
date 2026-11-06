import Mathlib

theorem inequalities_90243 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (b * a) ≥ a + b + c := by

  have h1 : a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (b * a) - (a + b + c) ≥ 0 := by
    have ha1 : 0 < a * b * c := by
      positivity

    have h2 : a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (b * a) - (a + b + c) =
        (a^4 + b^4 + c^4 - (a + b + c) * (a * b * c)) / (a * b * c) := by
      field_simp
      ring

    rw [h2] at *
   

    have h3 : a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c) := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
                  sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                  sq_nonneg (a * (a - b) + a * (a - c) + b * (b - a) + b * (b - c) + c * (c - a) + c * (c - b)), 
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

    have h4 : a^4 + b^4 + c^4 - (a + b + c) * (a * b * c) ≥ 0 := by
      nlinarith [h3]

    have h5 : (a^4 + b^4 + c^4 - (a + b + c) * (a * b * c)) / (a * b * c) ≥ 0 := by
      apply div_nonneg
      linarith [h4]
      all_goals
        positivity
    linarith
  linarith [h1]