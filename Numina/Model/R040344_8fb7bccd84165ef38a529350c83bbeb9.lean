import Mathlib

open Real

theorem inequalities_126469 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a ≥ 1) :
    1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ sqrt 3 / (a * b * c) := by
  have h1 : 0 < a * b * c := by positivity
  have h2 : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 - sqrt 3 / (a * b * c) ≥ 0 := by
    have h3 : 0 < a * b * c := by positivity
    have h4 : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 - sqrt 3 / (a * b * c) =
        ( (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 ) - sqrt 3 * (a * b * c) ) / ( a^2 * b^2 * c^2 ) := by
      field_simp
      ring
    rw [h4]
    apply div_nonneg
    -- Prove the numerator is non-negative
    have h5 : (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 ) ≥ sqrt 3 * (a * b * c) := by
      have h6 : (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 ) ^ 2 ≥ 3 * (a * b * c) ^ 2 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * b * c), 
          sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a),
          mul_nonneg (show (0 : ℝ) ≤ a * b by positivity) (show (0 : ℝ) ≤ b * c by positivity),
          mul_nonneg (show (0 : ℝ) ≤ a * b by positivity) (show (0 : ℝ) ≤ c * a by positivity),
          mul_nonneg (show (0 : ℝ) ≤ b * c by positivity) (show (0 : ℝ) ≤ c * a by positivity)
        ]
      have h7 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h8 : (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 ) ≥ 0 := by positivity
      have h9 : sqrt 3 * (a * b * c) ≥ 0 := by
        have h14 : sqrt 3 ≥ 0 := by positivity
        have h15 : a * b * c > 0 := by positivity
        nlinarith
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 - sqrt 3 * (a * b * c)), sq_nonneg (sqrt 3 * (a * b * c) - (b^2 * c^2 + a^2 * c^2 + a^2 * b^2)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    linarith
    all_goals positivity
  linarith