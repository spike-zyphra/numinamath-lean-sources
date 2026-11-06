import Mathlib

open Real
open scoped BigOperators

theorem inequalities_112393 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (x : ℝ) (hx : x = a / (a + 2 * b) + b / (b + 2 * c) + c / (c + 2 * a)) :
  1 ≤ x := by
    rw [hx]
    have ha1 : 0 < a := by linarith
    have hb1 : 0 < b := by linarith
    have hc1 : 0 < c := by linarith
    have h1 : 0 < a + 2 * b := by nlinarith
    have h2 : 0 < b + 2 * c := by nlinarith
    have h3 : 0 < c + 2 * a := by nlinarith
    have h4 : a / (a + 2 * b) + b / (b + 2 * c) + c / (c + 2 * a) - 1 ≥ 0 := by
      have pos1 : 0 < (a + 2 * b) * (b + 2 * c) * (c + 2 * a) := by positivity
      have eq1 : (a / (a + 2 * b) + b / (b + 2 * c) + c / (c + 2 * a) - 1) = ( (a * (b + 2 * c) * (c + 2 * a) + b * (a + 2 * b) * (c + 2 * a) + c * (a + 2 * b) * (b + 2 * c) - (a + 2 * b) * (b + 2 * c) * (c + 2 * a)) / ((a + 2 * b) * (b + 2 * c) * (c + 2 * a)) ) := by
        field_simp
        ring
      rw [eq1]
      have eq2 : (a * (b + 2 * c) * (c + 2 * a) + b * (a + 2 * b) * (c + 2 * a) + c * (a + 2 * b) * (b + 2 * c) - (a + 2 * b) * (b + 2 * c) * (c + 2 * a)) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      apply div_nonneg
      linarith
      positivity
    linarith [h4]