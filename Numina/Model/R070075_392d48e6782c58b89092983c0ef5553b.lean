import Mathlib

theorem algebra_2539 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
(h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
-(a + b + c) + abs (a - b - c) - abs (b - c - a) + abs (c - b - a) = 2*(b-a-c) := by 
  have h1 : a - b - c < 0 := by linarith
  have h2 : b - c - a < 0 := by linarith
  have h3 : c - b - a < 0 := by linarith
  rw [abs_of_neg h1, abs_of_neg h2, abs_of_neg h3]
  ring