import Mathlib

theorem algebra_206282 (a b c : ℝ) :
    (∀ x y : ℝ, x^2 + x * y + y^2 + a * x + b * y + c > 0) ↔
    a^2 - a * b + b^2 < 3 * c := by
  constructor
  · -- Assume that for all real numbers x and y, x^2 + x*y + y^2 + a*x + b*y + c > 0, derive a^2 - a*b + b^2 < 3*c
    intro h
    have h1 := h ((b - 2 * a) / 3) ((- (2 * b - a) ) / 3)
    have h2 : - (a ^ 2 - a * b + b ^ 2) / 3 + c > 0 := by
      nlinarith [sq_nonneg ( (b - 2 * a : ℝ) / 3 ), sq_nonneg ( (2 * b - a : ℝ) / 3 ), sq_nonneg ( (a - b : ℝ) ), sq_nonneg ( (a : ℝ) ), sq_nonneg ( (b : ℝ) ), h1 ]
    nlinarith 
  · -- Assume a^2 - a*b + b^2 < 3*c, prove that ∀ x y : ℝ, x^2 + x * y + y^2 + a * x + b * y + c > 0 
    intro h x y
    have h_pos : x ^ 2 + x * y + y ^ 2 + a * x + b * y + c > 0 := by
      nlinarith [sq_nonneg (x - (b - 2 * a) / 3 ), sq_nonneg (y - (- (2 * b - a) / 3 ) ), sq_nonneg ( (a - b) ), sq_nonneg ( (a : ℝ) ), sq_nonneg ( (b : ℝ) ), sq_nonneg (x + y/2), sq_nonneg ((y + (x - a))/2) ]
    linarith