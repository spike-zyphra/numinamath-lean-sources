import Mathlib
open Real

theorem inequality_605437 (a b : ℝ) (h : a * b ≥ 1) (ha : a > 0) (hb : b > 0):
(a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) ≥ 16 := by
  have ha1 : a + 1 > 0 := by linarith
  have hb1 : b + 1 > 0 := by linarith
  have h2 : (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) =
      (a + 2 * b) * (b + 2 * a) + (a + 2 * b) * (2 / (b + 1)) + (2 / (a + 1)) * (b + 2 * a) + (2 / (a + 1)) * (2 / (b + 1)) := by ring
  rw [h2]
  have h4 : 0 < (a + 1) * (b + 1) := by positivity
  have h5 : (a + 2 * b) * (b + 2 * a) + (a + 2 * b) * (2 / (b + 1)) + (2 / (a + 1)) * (b + 2 * a) + (2 / (a + 1)) * (2 / (b + 1)) - 16 ≥ 0 := by
    have h6 : (a + 2 * b) * (b + 2 * a) + (a + 2 * b) * (2 / (b + 1)) + (2 / (a + 1)) * (b + 2 * a) + (2 / (a + 1)) * (2 / (b + 1)) - 16 =
        ((a + 2 * b) * (b + 2 * a) * (a + 1) * (b + 1) + (a + 2 * b) * 2 * (a + 1) + 2 * (b + 2 * a) * (b + 1) + 4 - 16 * (a + 1) * (b + 1)) / ((a + 1) * (b + 1)) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1),
      sq_nonneg (a - b), sq_nonneg ((a + 1) - (b + 1)), sq_nonneg (a * (b - 1)), sq_nonneg (b * (a - 1)),
      mul_pos ha hb, mul_pos ha (show 0 < a * b from by nlinarith), mul_pos hb (show 0 < a * b from by nlinarith)]
    all_goals
      positivity
  linarith