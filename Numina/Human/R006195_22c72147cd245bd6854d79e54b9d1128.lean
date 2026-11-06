import Mathlib

open Real
open scoped BigOperators

theorem algebra_2211 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  abs (a + b + c) - abs (a - b - c) - abs (a - b + c) - abs (a + b - c) = 0 := by
    have h1 : a + b + c > 0 := by linarith
    have h2 : a - b - c < 0 := by linarith
    have h3 : a - b + c > 0 := by linarith
    have h4 : a + b - c > 0 := by linarith
    calc
      abs (a + b + c) - abs (a - b - c) - abs (a - b + c) - abs (a + b - c)
          = (a + b + c) - abs (a - b - c) - abs (a - b + c) - abs (a + b - c) := by
            rw [abs_of_pos h1]
      _ = (a + b + c) - (-(a - b - c)) - abs (a - b + c) - abs (a + b - c) := by
            rw [abs_of_neg h2]
      _ = (a + b + c) - (-(a - b - c)) - (a - b + c) - abs (a + b - c) := by
            rw [abs_of_pos h3]
      _ = (a + b + c) - (-(a - b - c)) - (a - b + c) - (a + b - c) := by
            rw [abs_of_pos h4]
      _ = 0 := by ring