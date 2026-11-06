import Mathlib

/- Multiplying or dividing both sides of an inequality by the same     will change the direction of the inequality. $ -/
theorem algebra_9405 {x y c : ℝ} (h : x < y) (hc : c < 0) : x * c > y * c ∧ x / c > y / c := by
  constructor
  . exact mul_lt_mul_of_neg_right h hc
  . exact div_lt_div_of_neg_of_lt hc h
