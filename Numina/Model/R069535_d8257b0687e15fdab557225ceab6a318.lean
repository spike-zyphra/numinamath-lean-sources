import Mathlib

theorem algebra_259064 {a b c x : ℝ} (h : a * x ^ 2 - b * x - c = b * x ^ 2 - c * x - a)
    (h' : b * x ^ 2 - c * x - a = c * x ^ 2 - a * x - b) :
    a = b ∧ b = c := by 
  have eq1 : (a - b) * x^2 + (c - b) * x + (a - c) = 0 := by 
    linarith [h]
  have eq2 : (b - c) * x^2 + (a - c) * x + (b - a) = 0 := by 
    linarith [h']
  constructor
  · nlinarith [sq_nonneg (x ^ 2 - x + 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 + x), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  · nlinarith [sq_nonneg (x ^ 2 - x + 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 + x), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]