import Mathlib

theorem inequalities_320556
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (b + c) / (2 * a) + (c + a) / (2 * b) + (a + b) / (2 * c) ≥
    2 * a / (b + c) + 2 * b / (c + a) + 2 * c / (a + b) := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : 0 < a * b := by
    positivity
  have h3 : 0 < a * c := by
    positivity
  have h4 : 0 < b * c := by
    positivity
  have h5 : 0 < (b + c) * (c + a) * (a + b) := by
    positivity
  have h8 : (b + c) / (2 * a) + (c + a) / (2 * b) + (a + b) / (2 * c) - (2 * a / (b + c) + 2 * b / (c + a) + 2 * c / (a + b)) ≥ 0 := by
    have h9 : 0 < (2 * a * b * c * (b + c) * (c + a) * (a + b)) := by
      positivity
    have h10 : (b + c) / (2 * a) + (c + a) / (2 * b) + (a + b) / (2 * c) - (2 * a / (b + c) + 2 * b / (c + a) + 2 * c / (a + b)) =
        ( (b + c)^2 * b * c * (c + a) * (a + b) + (c + a)^2 * a * c * (b + c) * (a + b) + (a + b)^2 * a * b * (b + c) * (c + a) - (4 * a^2 * b * c * (c + a) * (a + b) + 4 * a * b^2 * c * (b + c) * (a + b) + 4 * a * b * c^2 * (b + c) * (c + a) )) / (2 * a * b * c * (b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h10] at *
    have h11 : ( (b + c)^2 * b * c * (c + a) * (a + b) + (c + a)^2 * a * c * (b + c) * (a + b) + (a + b)^2 * a * b * (b + c) * (c + a) - (4 * a^2 * b * c * (c + a) * (a + b) + 4 * a * b^2 * c * (b + c) * (a + b) + 4 * a * b * c^2 * (b + c) * (c + a) )) ≥ 0 := by
      have h3 : 0 < a * b * c := by
        positivity
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                  sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
                  sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
                  sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < b + c by positivity) (show 0 < c + a by positivity), mul_pos (show 0 < c + a by positivity) (show 0 < a + b by positivity), mul_pos (show 0 < a + b by positivity) (show 0 < b + c by positivity),
                  sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                  sq_nonneg (a * (a * b - b * c)), sq_nonneg (b * (b * c - c * a)), sq_nonneg (c * (c * a - a * b))]
    have h12 : ( (b + c)^2 * b * c * (c + a) * (a + b) + (c + a)^2 * a * c * (b + c) * (a + b) + (a + b)^2 * a * b * (b + c) * (c + a) - (4 * a^2 * b * c * (c + a) * (a + b) + 4 * a * b^2 * c * (b + c) * (a + b) + 4 * a * b * c^2 * (b + c) * (c + a) )) / (2 * a * b * c * (b + c) * (c + a) * (a + b)) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith