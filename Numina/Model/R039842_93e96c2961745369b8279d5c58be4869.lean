import Mathlib

open Real

theorem inequalities_178178 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 / (b^3 * c) - a / b^2 ≥ c / b - c^2 / a := by
  have h1 : 0 < a * b^3 * c := by positivity
  have h2 : a^2 / (b^3 * c) - a / b^2 - (c / b - c^2 / a) ≥ 0 := by
    have h3 : a^2 / (b^3 * c) - a / b^2 - (c / b - c^2 / a) = 
        (a^3 - a * (a * b * c) - a * b^2 * c^2 + c^3 * b^3) / (a * b^3 * c) := by 
      field_simp
      ring
    rw [h3]
    have h4 : a^3 - a * (a * b * c) - a * b^2 * c^2 + c^3 * b^3 ≥ 0 := by
      nlinarith [sq_nonneg (a - b * c), sq_nonneg (a + b * c), sq_nonneg (b * c - a), sq_nonneg (a^2 - b^2 * c^2), 
          sq_nonneg (a * (a - b * c)), sq_nonneg ((b * c) * (a - b * c)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    have h5 : (a^3 - a * (a * b * c) - a * b^2 * c^2 + c^3 * b^3) / (a * b^3 * c) ≥ 0 := by
      apply div_nonneg 
      linarith 
      all_goals linarith
    linarith 
  linarith