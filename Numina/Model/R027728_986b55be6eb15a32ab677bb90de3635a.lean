import Mathlib

theorem inequalities_34959 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    2/3 ≤ a/(b+2*c+3*d) + b/(c+2*d+3*a) + c/(d+2*a+3*b) + d/(a+2*b+3*c) := by
  have h₁ : 0 < b + 2 * c + 3 * d := by positivity
  have h₂ : 0 < c + 2 * d + 3 * a := by positivity
  have h₃ : 0 < d + 2 * a + 3 * b := by positivity
  have h₄ : 0 < a + 2 * b + 3 * c := by positivity
  have h5 : a/(b+2*c+3*d) + b/(c+2*d+3*a) + c/(d+2*a+3*b) + d/(a+2*b+3*c) - 2/3 ≥ 0 := by
    have h6 : a / (b + 2 * c + 3 * d) + b / (c + 2 * d + 3 * a) + c / (d + 2 * a + 3 * b) + d / (a + 2 * b + 3 * c) - 2 / 3 =
        (a * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c) +
         b * (b + 2 * c + 3 * d) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c) +
         c * (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (a + 2 * b + 3 * c) +
         d * (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) - 2 / 3 * ((b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c))) / ((b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c)) := by
      field_simp
      <;> ring
    rw [h6]
    apply div_nonneg
    · -- Show numerator is non-negative 
      have h7 : a * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c) + 
          b * (b + 2 * c + 3 * d) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c) + 
          c * (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (a + 2 * b + 3 * c) + 
          d * (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) - 2 / 3 * ((b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c)) ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
                  sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
                  mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
                  sq_nonneg (a + b + c + d), 
                  sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
                  sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
                  mul_pos (show 0 < a * b from by nlinarith) (show 0 < c * d from by nlinarith), 
                  mul_pos (show 0 < a * c from by nlinarith) (show 0 < b * d from by nlinarith)
                  ]
      nlinarith
    · -- Show denominator is positive
      positivity
  linarith