import Mathlib

/-Given that a b c d e and f are integers and 
(a * x + b * y + c) * (d * x + e * y - f) = 2 * x ^ 2 - 5 * x * y + 3 * y ^ 2 - 19 * x - 25 * y + 42 find the maximum value of
a+b+c+d+e+f-/
theorem algebra_3344 (a b c d e f : ℤ) (h : ∀ x y : ℤ, (a * x + b * y + c) * (d * x + e * y - f) = 2 * x ^ 2 - 5 * x * y + 3 * y ^ 2 - 19 * x - 25 * y + 42) :
    a + b + c + d + e + f ≤ 12 := by

    -- evaluate at some particular points to get a system of equations 
  have eq1 := h 0 0
  have eq2 := h 1 0
  have eq3 := h 0 1
  have eq4 := h 1 1
  have eq5 := h 2 0
  have eq6 := h 0 2
  have eq7 := h 1 2
  ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 eq7
  
  have h1 : c * f = -42 := by nlinarith
  
  nlinarith [sq_nonneg (a * 0 + b * 0 + c), sq_nonneg (d * 0 + e * 0 - f), sq_nonneg (a * 1 + b * 0 + c), sq_nonneg (d * 1 + e * 0 - f),
          sq_nonneg (a * 0 + b * 1 + c), sq_nonneg (d * 0 + e * 1 - f), sq_nonneg (a * 1 + b * 1 + c), sq_nonneg (d * 1 + e * 1 - f),
          sq_nonneg (a * 2 + b * 0 + c), sq_nonneg (d * 2 + e * 0 - f), sq_nonneg (a * 0 + b * 2 + c), sq_nonneg (d * 0 + e * 2 - f),
          sq_nonneg (a * 1 + b * 2 + c), sq_nonneg (d * 1 + e * 2 - f)]