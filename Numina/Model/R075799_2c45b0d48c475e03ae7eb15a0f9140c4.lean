import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_597577 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b - c = 1) (h' : a > b) (h'' : √(a^2 + b^2 + c^2) = 1) :
  0 < c ∧ c < 1 / 3 := by
  have h2 : a^2 + b^2 + c^2 = 1 := by
    calc
      a^2 + b^2 + c^2 = (√(a^2 + b^2 + c^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 1 ^ 2 := by rw [h'']
      _ = 1 := by norm_num
  have h3 : a + b = 1 + c := by linarith
  have h4 : a * b = c^2 + c := by
    nlinarith [h3, h2]
  have h5 : (a - b) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero
    linarith
  have h7 : 3 * c^2 + 2 * c - 1 < 0 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, h5, h3, h2, h4]
  have h8 : c < 1 / 3 := by
    nlinarith [sq_pos_of_pos hc, h7]
  constructor
  · linarith
  · linarith