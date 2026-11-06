import Mathlib

theorem algebra_64565 {a b c : ℝ} (h : a ≠ b ∧ b ≠ c ∧ a ≠ c)
    (h1 : (X - a) * (X - b) * (X - c) = X^3 + p*X^2 + q*X + r)
    (h2 : X^3 + p*X^2 + q*X + r = 91) (h3 : X^3 + p*X^2 + q*X + r = -121) :
    (a*b + b*c + c*a)/(a*b*c + a + b + c) ≤ 7 := by
  linarith