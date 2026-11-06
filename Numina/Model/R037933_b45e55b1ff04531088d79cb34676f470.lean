import Mathlib

theorem algebra_228704 (a : ℝ) (ha : a > 0) (x y : ℝ) (hy : x > y) :
    (a > 1 → a ^ x > a ^ y) ∧ (a < 1 → a ^ x < a ^ y) := by
  constructor
  · -- First implication: if a > 1, then a ^ x > a ^ y
    intro ha1
    have h : a ^ y < a ^ x := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      all_goals linarith
    linarith
  · -- Second implication: if a < 1, then a ^ x < a ^ y
    intro ha2
    have h : a ^ x < a ^ y := by
      apply Real.rpow_lt_rpow_of_exponent_gt
      all_goals nlinarith
    linarith