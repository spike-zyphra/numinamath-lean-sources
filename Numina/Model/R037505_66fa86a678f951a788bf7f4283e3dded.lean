import Mathlib
theorem inequalities_1674 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * (a + b + c)^3 ≥ 3 * (a^2 + b^2 + c^2 + a * b + b * c + c * a) *
      Real.sqrt (3 * (a * b + b * c + c * a)) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha
  have h4 : 0 < 3 * (a * b + b * c + c * a) := by nlinarith
  have h5 : 0 < Real.sqrt (3 * (a * b + b * c + c * a)) := by
    apply Real.sqrt_pos.mpr
    linarith
  have h6 : (Real.sqrt (3 * (a * b + b * c + c * a)))^2 = 3 * (a * b + b * c + c * a) := Real.sq_sqrt (by nlinarith)
  nlinarith [sq_nonneg (2 * (a + b + c)^3 - 3 * (a^2 + b^2 + c^2 + a * b + b * c + c * a) * Real.sqrt (3 * (a * b + b * c + c * a))), 
          sq_nonneg (Real.sqrt (3 * (a * b + b * c + c * a)) - (a + b + c)),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          Real.sqrt_nonneg (3 * (a * b + b * c + c * a)),
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 * (a * b + b * c + c * a) by positivity),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          sq_nonneg ( (a + b + c)^2 - 3 * (a * b + b * c + c * a) )
        ]