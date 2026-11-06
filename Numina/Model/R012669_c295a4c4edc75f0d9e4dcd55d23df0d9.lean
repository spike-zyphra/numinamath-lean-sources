import Mathlib

open Real
open scoped BigOperators

theorem inequalities_160519 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : 0 < (a + b - c) * (b + c - a) * (c + a - b) := by
    have h1 : 0 < a + b - c := by linarith
    have h2 : 0 < b + c - a := by linarith
    have h3 : 0 < c + a - b := by linarith
    positivity

  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
    sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
    sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
    mul_pos (sub_pos.mpr (show a + b > c by linarith)) 
      (sub_pos.mpr (show b + c > a by linarith)), 
    mul_pos (sub_pos.mpr (show b + c > a by linarith)) 
      (sub_pos.mpr (show c + a > b by linarith)), 
    mul_pos (sub_pos.mpr (show c + a > b by linarith)) 
      (sub_pos.mpr (show a + b > c by linarith))
  ]