import Mathlib

open Real
open scoped BigOperators

theorem inequalities_143637 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : a^2 + b^2 > 5 * c^2) :
  c < a ∧ c < b := by

  have h1 : c < a := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, h, h', h'', h''']
  
  have h2 : c < b := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, h, h', h'', h''']
  
  constructor
  · linarith [h1]
  · linarith [h2]