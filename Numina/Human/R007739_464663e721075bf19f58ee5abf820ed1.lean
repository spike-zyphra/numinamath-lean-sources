import Mathlib

/- If the sum of the squares of nonnegative real numbers $a,b,$ and $c$ is $13$, and $ab + bc + ca = 6$, then what is the sum of $a,b,$ and $c$? -/
theorem algebra_20734 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h₀ : a^2 + b^2 + c^2 = 13) (h₁ : a * b + b * c + c * a = 6) :
    a + b + c = 5 := by
  nlinarith [sq_nonneg (a + b + c)]