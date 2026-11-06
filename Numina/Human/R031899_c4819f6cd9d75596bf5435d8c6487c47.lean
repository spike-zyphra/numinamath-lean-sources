import Mathlib

/- Let $a, b, c,$ and $d$ be real numbers such that $a \geq b \geq c \geq d$ and
$$a+b+c+d = 13$$
$$a^2+b^2+c^2+d^2=43.$$

Show that $ab \geq 3 + cd$.
 -/
theorem inequalities_49841 (a b c d : ℝ) (h₀ : a ≥ b ∧ b ≥ c ∧ c ≥ d)
    (h₁ : a + b + c + d = 13) (h₂ : a^2 + b^2 + c^2 + d^2 = 43) :
    a * b ≥ 3 + c * d := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (a - c + b - d)]