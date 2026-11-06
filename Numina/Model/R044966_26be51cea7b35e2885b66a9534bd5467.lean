import Mathlib
open Real
theorem inequalities_72088 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) : logb a (b * c) + logb b (c * a) + logb c (a * b) ≥ 4 * logb (a * b) c + 4 * logb (b * c) a + 4 * logb (c * a) b:= by

  have ha1 : 0 < a := by linarith
  have hb1 : 0 < b := by linarith
  have hc1 : 0 < c := by linarith

  have h1 : logb a (b * c) = (log (b * c) ) / (log a) := by field_simp [logb]
  have h2 : log (b * c) = log b + log c := by rw [log_mul (by linarith) (by linarith)]
  have h3 : logb b (c * a) = (log (c * a) ) / (log b) := by field_simp [logb]
  have h4 : log (c * a) = log c + log a := by rw [log_mul (by linarith) (by linarith)]
  have h5 : logb c (a * b) = (log (a * b) ) / (log c) := by field_simp [logb]
  have h6 : log (a * b) = log a + log b := by rw [log_mul (by linarith) (by linarith)]
  have h7 : logb (a * b) c = (log c) / (log (a * b)) := by field_simp [logb]
  have h8 : log (a * b) = log a + log b := by rw [log_mul (by linarith) (by linarith)]
  have h9 : logb (b * c) a = (log a) / (log (b * c)) := by field_simp [logb]
  have h10 : log (b * c) = log b + log c := by rw [log_mul (by linarith) (by linarith)]
  have h11 : logb (c * a) b = (log b) / (log (c * a)) := by field_simp [logb]
  have h12 : log (c * a) = log c + log a := by rw [log_mul (by linarith) (by linarith)]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

  have ha2 : 0 < log a := by apply log_pos; linarith
  have hb2 : 0 < log b := by apply log_pos; linarith
  have hc2 : 0 < log c := by apply log_pos; linarith
  have hf1 : log a + log b > 0 := by nlinarith
  have hf2 : log b + log c > 0 := by nlinarith
  have hf3 : log c + log a > 0 := by nlinarith

  have h13 : (log b + log c) / log a + (log c + log a) / log b + (log a + log b) / log c ≥ 4 * (log c / (log a + log b) + log a / (log b + log c) + log b / (log c + log a)) := by
    have h14 : 0 < log a * log b * log c * (log a + log b) * (log b + log c) * (log c + log a) := by positivity
    have h15 : (log b + log c) / log a + (log c + log a) / log b + (log a + log b) / log c - 4 * (log c / (log a + log b) + log a / (log b + log c) + log b / (log c + log a)) ≥ 0 := by
      have h16 : (log b + log c) / log a + (log c + log a) / log b + (log a + log b) / log c - 4 * (log c / (log a + log b) + log a / (log b + log c) + log b / (log c + log a)) =
        ( (log b + log c) * (log b * log c * (log a + log b) * (log b + log c) * (log c + log a)) +
        (log c + log a) * (log a * log c * (log a + log b) * (log b + log c) * (log c + log a)) +
        (log a + log b) * (log a * log b * (log a + log b) * (log b + log c) * (log c + log a)) -
        4 * ( log c * (log a * log b * log c * (log b + log c) * (log c + log a)) +
        log a * (log a * log b * log c * (log a + log b) * (log c + log a)) +
        log b * (log a * log b * log c * (log a + log b) * (log b + log c) ) ) ) /
        ( log a * log b * log c * (log a + log b) * (log b + log c) * (log c + log a) ) := by
        field_simp
        ring
      rw [h16] at *
      apply div_nonneg
      · -- Show numerator is non-negative
        nlinarith [ sq_nonneg (log a * log b - log a * log c),
            sq_nonneg (log a * log b - log b * log c),
            sq_nonneg (log b * log c - log a * log c),
            sq_nonneg (log a - log b), sq_nonneg (log b - log c), sq_nonneg (log c - log a),
            sq_nonneg (log a * (log a - log b)), sq_nonneg (log a * (log a - log c)),
            sq_nonneg (log b * (log b - log a)), sq_nonneg (log b * (log b - log c)),
            sq_nonneg (log c * (log c - log a)), sq_nonneg (log c * (log c - log b)),
            mul_pos ha2 hb2, mul_pos hb2 hc2, mul_pos ha2 hc2,
            mul_pos (show 0 < log a + log b by positivity) (show 0 < log b + log c by positivity),
            mul_pos (show 0 < log b + log c by positivity) (show 0 < log c + log a by positivity),
            mul_pos (show 0 < log c + log a by positivity) (show 0 < log a + log b by positivity) ]
      · -- Show denominator is non-negative
        positivity
    linarith

  linarith