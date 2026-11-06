import Mathlib

open Real

theorem inequalities_260438 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1) ≤ 1 / 2 := by 
  have h1 : 2 * a + 1 > 0 := by nlinarith
  have h2 : 3 * b + 1 > 0 := by nlinarith
  have h3 : 6 * c + 1 > 0 := by nlinarith
  
  have h4 : a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1) - 1 / 2 ≤ 0 := by
    have h5 : (2 * a + 1) * (3 * b + 1) * (6 * c + 1) > 0 := by positivity
    have eq1 : (a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1) - 1 / 2) =
        (a * (3 * b + 1) * (6 * c + 1) + b * (2 * a + 1) * (6 * c + 1) + c * (2 * a + 1) * (3 * b + 1) - 1 / 2 * (2 * a + 1) * (3 * b + 1) * (6 * c + 1)) / ((2 * a + 1) * (3 * b + 1) * (6 * c + 1)) := by
      field_simp
      <;> ring
    rw [eq1]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that numerator is non-positive
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 6),
        h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    · -- Show that denominator is non-negative
      positivity
  
  -- Use h4 to conclude the desired inequality
  linarith [show a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1) - 1 / 2 ≤ 0 by linarith [h4]]