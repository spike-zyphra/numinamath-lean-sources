import Mathlib

/- If the sum of the squares of nonnegative real numbers $a,b,$ and $c$ is $39$, and $ab + bc + ca = 21$, then what is the sum of $a,b,$ and $c$? -/
theorem algebra_12959 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a^2 + b^2 + c^2 = 39) (h2 : a * b + b * c + c * a = 21) :
    a + b + c = 9 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]