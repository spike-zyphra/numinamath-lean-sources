import Mathlib

theorem algebra_323767 (a b c d : ℝ) (h : (1^4 + a * 1^3 + b * 1^2 + c * 1 + d) = 10)
    (h' : (2^4 + a * 2^3 + b * 2^2 + c * 2 + d) = 20) (h'' : (3^4 + a * 3^3 + b * 3^2 + c * 3 + d) = 30) :
    (10^4 + a * 10^3 + b * 10^2 + c * 10 + d) + ( (-6)^4 + a * (-6)^3 + b * (-6)^2 + c * (-6) + d) = 8104 := by
  ring_nf at h h' h'' ⊢
  linarith