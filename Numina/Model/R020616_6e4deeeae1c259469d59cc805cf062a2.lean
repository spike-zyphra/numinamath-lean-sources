import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_305148 (a : ℝ) :
  (∀ x y, x - y ≤ 0 → x + y - 5 ≥ 0 → y - 3 ≤ 0 → a * (x^2 + y^2) ≤ (x + y)^2) ↔
  a ≤ 25 / 13 := by
  constructor
  · -- Assume the inequality holds, prove a ≤ 25/13
    intro h
    have h1 := h 2 3 (by norm_num) (by norm_num) (by norm_num)
    nlinarith
  · -- Show that if a ≤ 25/13, the inequality holds
    intro ha x y h1 h2 h3
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (x - y), sq_nonneg (x + y - 5), sq_nonneg (x - 2.5), sq_nonneg (y - 2.5), 
        mul_nonneg (show 0 ≤ (0 : ℝ) by linarith) (show 0 ≤ (0 : ℝ) by linarith)
      ]