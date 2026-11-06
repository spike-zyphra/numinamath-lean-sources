import Mathlib

theorem inequalities_603551 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 5 ≤ (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) +
           (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) +
           (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h2 : (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) - 3 / 5 ≥ 0 := by 
    have pos1 : (b + c) ^ 2 + a ^ 2 > 0 := by positivity
    have pos2 : (c + a) ^ 2 + b ^ 2 > 0 := by positivity
    have pos3 : (a + b) ^ 2 + c ^ 2 > 0 := by positivity
    have h2' : (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) - 3 / 5 =
        (5 * ((b + c - a) ^ 2 * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) +
           (c + a - b) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((a + b) ^ 2 + c ^ 2) +
           (a + b - c) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2)) - 3 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) / (5 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) := by
      field_simp
      ring
    rw [h2']
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha (show 0 < b by linarith),
          mul_pos ha (show 0 < c by linarith),
          mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
    positivity
  linarith