import Mathlib

open Real

theorem inequalities_600468 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    logb a (b * c) + logb b (c * a) + logb c (a * b) ≥
    4 * (logb (a * b) c + logb (b * c) a + logb (c * a) b) := by

  have h1 : 1 < a * b := by nlinarith
  have h2 : 1 < b * c := by nlinarith
  have h3 : 1 < c * a := by nlinarith

  have h4 : logb a (b * c) = (log (b * c) ) / (log a) := by
    field_simp [logb]

  have h5 : logb b (c * a) = (log (c * a) ) / (log b) := by
    field_simp [logb]

  have h6 : logb c (a * b) = (log (a * b) ) / (log c) := by
    field_simp [logb]

  have h7 : logb (a * b) c = (log c ) / (log (a * b) ) := by
    field_simp [logb]

  have h8 : logb (b * c) a = (log a ) / (log (b * c) ) := by
    field_simp [logb]

  have h9 : logb (c * a) b = (log b ) / (log (c * a) ) := by
    field_simp [logb]

  have h10 : log (b * c) = log b + log c := by
    rw [log_mul (by linarith) (by linarith)]

  have h11 : log (c * a) = log c + log a := by
    rw [log_mul (by linarith) (by linarith)]

  have h12 : log (a * b) = log a + log b := by
    rw [log_mul (by linarith) (by linarith)]

  rw [h4, h5, h6, h7, h8, h9, h10, h11, h12]

  have h13 : log a > 0 := by apply log_pos; linarith
  have h14 : log b > 0 := by apply log_pos; linarith
  have h15 : log c > 0 := by apply log_pos; linarith

  have h19 : (log b + log c) / (log a) + (log c + log a) / (log b) + (log a + log b) / (log c) ≥ 4 * (log c / (log a + log b) + log a / (log b + log c) + log b / (log c + log a)) := by

    have h21 : (log b + log c) / (log a) + (log c + log a) / (log b) + (log a + log b) / (log c) - 4 * (log c / (log a + log b) + log a / (log b + log c) + log b / (log c + log a)) ≥ 0 := by

      have h22 : (log b + log c) / (log a) + (log c + log a) / (log b) + (log a + log b) / (log c) - 4 * (log c / (log a + log b) + log a / (log b + log c) + log b / (log c + log a)) =
          ((log b + log c) * (log b * log c * (log a + log b) * (log b + log c) * (log c + log a)) +
          (log c + log a) * (log a * log c * (log a + log b) * (log b + log c) * (log c + log a)) +
          (log a + log b) * (log a * log b * (log a + log b) * (log b + log c) * (log c + log a)) -
          4 * (log c * (log a * log b * log c * (log b + log c) * (log c + log a)) +
          log a * (log a * log b * log c * (log a + log b) * (log c + log a)) +
          log b * (log a * log b * log c * (log a + log b) * (log b + log c)))) / (log a * log b * log c * (log a + log b) * (log b + log c) * (log c + log a) ) := by
        field_simp
        ring
      rw [h22]

      have h20 : 0 < log a * log b * log c * (log a + log b) * (log b + log c) * (log c + log a) := by
        positivity

      have h23 : (log b + log c) * (log b * log c * (log a + log b) * (log b + log c) * (log c + log a)) +
          (log c + log a) * (log a * log c * (log a + log b) * (log b + log c) * (log c + log a)) +
          (log a + log b) * (log a * log b * (log a + log b) * (log b + log c) * (log c + log a)) -
          4 * (log c * (log a * log b * log c * (log b + log c) * (log c + log a)) +
          log a * (log a * log b * log c * (log a + log b) * (log c + log a)) +
          log b * (log a * log b * log c * (log a + log b) * (log b + log c))) ≥ 0 := by

        nlinarith [sq_nonneg (log a * (log b + log c) - log b * (log c + log a)), sq_nonneg (log b * (log c + log a) - log c * (log a + log b)), sq_nonneg (log c * (log a + log b) - log a * (log b + log c)),
          sq_nonneg (log a - log b), sq_nonneg (log b - log c), sq_nonneg (log c - log a),
          sq_nonneg (log a * (log b - log c)), sq_nonneg (log b * (log c - log a)), sq_nonneg (log c * (log a - log b)),
          mul_pos h13 h14, mul_pos h14 h15, mul_pos h13 h15, mul_pos (show 0 < log a + log b by linarith) (show 0 < log b + log c by linarith), mul_pos (show 0 < log b + log c by linarith) (show 0 < log c + log a by linarith), mul_pos (show 0 < log c + log a by linarith) (show 0 < log a + log b by linarith)]

      apply div_nonneg
      linarith
      all_goals
        positivity

    linarith

  linarith