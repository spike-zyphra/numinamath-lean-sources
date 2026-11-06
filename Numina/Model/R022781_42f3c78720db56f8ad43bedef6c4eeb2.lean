import Mathlib

theorem inequalities_110001 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 4) :
    1 ≤ a^3 / (b + 3 * c) + b^3 / (c + 3 * a) + c^3 / (a + 3 * b) := by

  have ha1 : a + 3 * b > 0 := by positivity
  have hb1 : b + 3 * c > 0 := by positivity
  have hc1 : c + 3 * a > 0 := by positivity
  
  have h1 : a^3 / (b + 3 * c) + b^3 / (c + 3 * a) + c^3 / (a + 3 * b) - 1 ≥ 0 := by
    have h2 : (a^3 / (b + 3 * c) + b^3 / (c + 3 * a) + c^3 / (a + 3 * b) - 1) =
        (a^3 * (c + 3 * a) * (a + 3 * b) + b^3 * (b + 3 * c) * (a + 3 * b) + c^3 * (b + 3 * c) * (c + 3 * a) - (b + 3 * c) * (c + 3 * a) * (a + 3 * b)) / ((b + 3 * c) * (c + 3 * a) * (a + 3 * b)) := by
      field_simp
      ring

    rw [h2]

    have pos1 : (b + 3 * c) * (c + 3 * a) * (a + 3 * b) > 0 := by positivity
    have h3 : a^3 * (c + 3 * a) * (a + 3 * b) + b^3 * (b + 3 * c) * (a + 3 * b) + c^3 * (b + 3 * c) * (c + 3 * a) - (b + 3 * c) * (c + 3 * a) * (a + 3 * b) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                sq_nonneg (a * (c + 3 * a) - b * (b + 3 * c)), sq_nonneg (b * (a + 3 * b) - c * (c + 3 * a)), sq_nonneg (c * (b + 3 * c) - a * (a + 3 * b)),
                sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                h]
    have h4 : (a^3 * (c + 3 * a) * (a + 3 * b) + b^3 * (b + 3 * c) * (a + 3 * b) + c^3 * (b + 3 * c) * (c + 3 * a) - (b + 3 * c) * (c + 3 * a) * (a + 3 * b)) / ((b + 3 * c) * (c + 3 * a) * (a + 3 * b)) ≥ 0 := by 
      apply div_nonneg
      linarith
      positivity
    linarith

  linarith