import Mathlib

theorem inequalities_49912 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3*a*b*c) :
    9/(a+b+c) ≤ a/(b^2*c^2) + b/(c^2*a^2) + c/(a^2*b^2) := by

  have h1 : 0 < a * b * c := by positivity
  have h2 : a + b + c > 0 := by positivity

  have h3 : a/(b^2*c^2) + b/(c^2*a^2) + c/(a^2*b^2) - 9/(a+b+c) ≥ 0 := by
    have h4 : 0 < a * b * c := h1
    have h5 : 0 < a^2 * b^2 * c^2 := by positivity
    have h7 : 0 < a^2 * b^2 * c^2 * (a + b + c) := by positivity
    have h8 : a/(b^2*c^2) + b/(c^2*a^2) + c/(a^2*b^2) - 9/(a+b+c) =
            ( (a^3*(a+b+c) + b^3*(a+b+c) + c^3*(a+b+c) - 9*(a^2*b^2*c^2) ) ) / ( a^2*b^2*c^2*(a+b+c ) ) := by
      field_simp
      ring
    rw [h8] at *
    have h9 : a^3*(a+b+c) + b^3*(a+b+c) + c^3*(a+b+c) - 9*(a^2*b^2*c^2) ≥ 0 := by
      nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        mul_pos (show 0 < a * b from by positivity) (show 0 < a * c from by positivity), 
        mul_pos (show 0 < a * b from by positivity) (show 0 < b * c from by positivity), 
        mul_pos (show 0 < a * c from by positivity) (show 0 < b * c from by positivity)
      ]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith