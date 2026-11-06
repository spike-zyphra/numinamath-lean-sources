import Mathlib

theorem inequalities_205258 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 1) :
    1 / (1 - a) + 1 / (1 - b) + 1 / (1 - c) ≥
    2 / (1 + a) + 2 / (1 + b) + 2 / (1 + c) := by

  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - b := by linarith
  have h3 : 0 < 1 - c := by linarith
  have h4 : 0 < 1 + a := by linarith
  have h5 : 0 < 1 + b := by linarith
  have h6 : 0 < 1 + c := by linarith

  have h7 : 1 / (1 - a) + 1 / (1 - b) + 1 / (1 - c) - (2 / (1 + a) + 2 / (1 + b) + 2 / (1 + c)) ≥ 0 := by

    have h8 : 1 / (1 - a) + 1 / (1 - b) + 1 / (1 - c) - (2 / (1 + a) + 2 / (1 + b) + 2 / (1 + c)) =
        ((1 * (1 - b) * (1 - c) * (1 + a) * (1 + b) * (1 + c)) +
        (1 * (1 - a) * (1 - c) * (1 + a) * (1 + b) * (1 + c)) +
        (1 * (1 - a) * (1 - b) * (1 + a) * (1 + b) * (1 + c)) -
        (2 * (1 - a) * (1 - b) * (1 - c) * (1 + b) * (1 + c)) -
        (2 * (1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + c)) -
        (2 * (1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + b))) / 
        ((1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + b) * (1 + c)) := by
      field_simp
      ring
    rw [h8] at *
    
    have h9 : (1 * (1 - b) * (1 - c) * (1 + a) * (1 + b) * (1 + c)) +
        (1 * (1 - a) * (1 - c) * (1 + a) * (1 + b) * (1 + c)) + 
        (1 * (1 - a) * (1 - b) * (1 + a) * (1 + b) * (1 + c)) - 
        (2 * (1 - a) * (1 - b) * (1 - c) * (1 + b) * (1 + c)) - 
        (2 * (1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + c)) - 
        (2 * (1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + b)) ≥ 0 := by

      have h10 : c = 1 - a - b := by linarith
      rw [h10]

      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_pos ha hb, mul_pos hb (show (0 : ℝ) < 1 - a - b by nlinarith), 
          mul_pos ha (show (0 : ℝ) < 1 - a - b by nlinarith), 
          sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - a * (1 - a - b)), sq_nonneg (a * (1 - a - b) - a * b)]
    
    have h10 : (1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + b) * (1 + c) > 0 := by
      positivity

    apply div_nonneg
    linarith
    all_goals
      linarith

  linarith