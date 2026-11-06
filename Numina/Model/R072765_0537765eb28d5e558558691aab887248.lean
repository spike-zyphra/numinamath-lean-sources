import Mathlib

theorem inequalities_598365 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3/2 ≤ a/(b+c) + b/(c+a) + c/(a+b) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a * c := mul_pos ha hc
  have h3 : 0 < b * c := mul_pos hb hc
  have h4 : 0 < (b + c) * (c + a) * (a + b) := by
    positivity
  have h5 : a/(b+c) + b/(c+a) + c/(a+b) - 3/2 ≥ 0 := by
    have h6 : (a/(b+c) + b/(c+a) + c/(a+b) - 3/2) =
        (2*a*(c+a)*(a+b) + 2*b*(b+c)*(a+b) + 2*c*(b+c)*(c+a) - 3*(b+c)*(c+a)*(a+b)) / (2*(b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h6]
    have h7 : 2*a*(c+a)*(a+b) + 2*b*(b+c)*(a+b) + 2*c*(b+c)*(c+a) - 3*(b+c)*(c+a)*(a+b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                  sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a*(a - b)), sq_nonneg (a*(a - c)),
                  sq_nonneg (b*(b - a)), sq_nonneg (b*(b - c)),
                  sq_nonneg (c*(c - a)), sq_nonneg (c*(c - b)),
                  mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith
  all_goals positivity