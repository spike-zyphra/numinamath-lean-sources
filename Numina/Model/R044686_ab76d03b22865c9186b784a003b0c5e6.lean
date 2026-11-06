import Mathlib

theorem inequalities_131001 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ (a^2 + b * c) / (a * (b + c)) + (b^2 + c * a) / (b * (c + a)) +
        (c^2 + a * b) / (c * (a + b)) := by
  have h2 : (a^2 + b * c) / (a * (b + c)) + (b^2 + c * a) / (b * (c + a)) + (c^2 + a * b) / (c * (a + b)) - 3 ≥ 0 := by
    have pos1 : 0 < a * (b + c) := by positivity
    have pos2 : 0 < b * (c + a) := by positivity
    have pos3 : 0 < c * (a + b) := by positivity
    have pos4 : 0 < a * (b + c) * b * (c + a) * c * (a + b) := by positivity

    have h3 : (a^2 + b * c) / (a * (b + c)) + (b^2 + c * a) / (b * (c + a)) + (c^2 + a * b) / (c * (a + b)) - 3 =
        ( (a^2 + b * c) * b * c * (c + a) * (a + b) + (b^2 + c * a) * a * c * (b + c) * (a + b) + (c^2 + a * b) * a * b * (b + c) * (c + a) - 3 * (a * (b + c) * b * (c + a) * c * (a + b)) ) / ( a * (b + c) * b * (c + a) * c * (a + b) ) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
              sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
              sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
            ]
    positivity
  linarith