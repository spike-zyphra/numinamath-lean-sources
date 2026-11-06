import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_159671 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
  (h : x + 2 * y = 1 / 2) :
  logb (1 / 2) (8 * x * y + 4 * y ^ 2 + 1) ≤ 0 := by
  have h4 : 8 * x * y + 4 * y^2 + 1 ≥ (1 : ℝ) := by
    nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (y - 1 / 4), h, sq_nonneg (x), sq_nonneg (y)]
  have hb : (1 / 2 : ℝ) > 0 := by norm_num
  have hbne : (1 / 2 : ℝ) ≠ 1 := by norm_num
  have ha : (8 * x * y + 4 * y^2 + 1 : ℝ) ≥ (1 : ℝ) := h4
  have h7 : logb (1 / 2) (8 * x * y + 4 * y^2 + 1) ≤ (0 : ℝ) := by
    have h8 : logb (1 / 2) (8 * x * y + 4 * y^2 + 1) = (log (8 * x * y + 4 * y^2 + 1) / log (1 / 2 : ℝ)) := by
      field_simp [logb]
    rw [h8]
    have h10 : log (1 / 2 : ℝ) < 0 := by
      have h11 : log (1 / 2 : ℝ) = log 1 - log 2 := by
        simp [log_div]
      rw [h11]
      have h12 : log 1 = 0 := Real.log_one
      have h13 : log 2 > 0 := by
        apply Real.log_pos
        norm_num
      linarith [h12, h13]
    have h14 : log (8 * x * y + 4 * y^2 + 1 : ℝ) ≥ (0 : ℝ) := by
      have h24 : (8 * x * y + 4 * y^2 + 1 : ℝ) ≥ (1 : ℝ) := h4
      have h15 : log (8 * x * y + 4 * y^2 + 1 : ℝ) ≥ log (1 : ℝ) := by
        apply Real.log_le_log
        all_goals nlinarith [h24]
      have h16 : log (1 : ℝ) = 0 := Real.log_one
      linarith [h15, h16]
    have h17 : (log (8 * x * y + 4 * y^2 + 1 : ℝ) / log (1 / 2 : ℝ)) ≤ (0 : ℝ) := by
      apply div_nonpos_of_nonneg_of_nonpos h14 (by linarith [h10])
    linarith [h17]
  linarith [h7]