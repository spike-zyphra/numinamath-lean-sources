import Mathlib

theorem algebra_324463 {a b c x1 y1 : ℝ} (h1 : a * x1 + b * y1 = 1) (h2 : b * x1 + c * y1 = 1)
    (h3 : c * x1 + a * y1 = 1) :
    a * b + b * c + c * a = a ^ 2 + b ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg (x1 - y1), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * x1 - b * y1), sq_nonneg (b * x1 - c * y1), sq_nonneg (c * x1 - a * y1)]