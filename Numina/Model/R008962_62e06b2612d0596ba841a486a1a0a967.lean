import Mathlib

theorem algebra_9405 {x y c : ℝ} (h : x < y) (hc : c < 0) : x * c > y * c ∧ x / c > y / c := by
  constructor
  · -- Proving x * c > y * c
    apply mul_lt_mul_of_neg_right
    exact h
    exact hc
  · -- Proving x / c > y / c
    apply div_lt_div_of_neg_of_lt
    all_goals
      linarith