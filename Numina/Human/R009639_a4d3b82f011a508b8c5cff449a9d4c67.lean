import Mathlib

/- In a history class, the probability of earning an A is .7 times the probability of earning a B, and the probability of earning a C is 1.4 times the probability of earning a B. Assuming that all grades are A, B, or C, how many B's will there be in a history class of 31 students? -/
theorem algebra_16821 (a b c : ℝ) (ha : a = 0.7 * b) (hc : c = 1.4 * b)
    (h : a + b + c = 1) (h' : 0 < b) (h'' : 0 < c) :
    b * 31 = 10 := by
  ring_nf at *
  linarith [h, h', h'']