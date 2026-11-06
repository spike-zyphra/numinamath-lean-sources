import Mathlib

open Real
open scoped BigOperators

theorem inequalities_227137 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  3 ≤ a / (b + c - a) + b / (c + a - b) + c / (a + b - c) := by
  have h1 : b + c - a > 0 := by linarith
  have h2 : c + a - b > 0 := by linarith
  have h3 : a + b - c > 0 := by linarith

  have h6 : a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3 ≥ 0 := by
    have h5 : (b + c - a) * (c + a - b) * (a + b - c) > 0 := by
      apply mul_pos
      apply mul_pos
      all_goals linarith

    have h6 : a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3 =
      (a * (c + a - b) * (a + b - c) + b * (b + c - a) * (a + b - c) + c * (b + c - a) * (c + a - b) - 3 * (b + c - a) * (c + a - b) * (a + b - c)) / ((b + c - a) * (c + a - b) * (a + b - c)) := by
      field_simp [h1, h2, h3]
      all_goals ring

    have h7 : a * (c + a - b) * (a + b - c) + b * (b + c - a) * (a + b - c) + c * (b + c - a) * (c + a - b) - 3 * (b + c - a) * (c + a - b) * (a + b - c) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                sq_nonneg ((a + b - c) - (b + c - a)), sq_nonneg ((b + c - a) - (c + a - b)), sq_nonneg ((c + a - b) - (a + b - c)), 
                mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3]

    have h11 : (a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3) = 
      (a * (c + a - b) * (a + b - c) + b * (b + c - a) * (a + b - c) + c * (b + c - a) * (c + a - b) - 3 * (b + c - a) * (c + a - b) * (a + b - c)) / ((b + c - a) * (c + a - b) * (a + b - c)) := by
      field_simp [h1, h2, h3]
      all_goals ring

    rw [h11]
    apply div_nonneg
    linarith
    all_goals linarith

  linarith