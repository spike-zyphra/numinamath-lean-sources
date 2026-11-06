import Mathlib

/- Let $a$ and $b$ be real numbers.  One of the roots of
\[x^3 + ax^2 - x + b = 0\]is $1 - 2i.$  Enter the ordered pair $(a,b).$ -/
theorem algebra_13456 (a b : ℝ) (h : (1 - 2 * Complex.I)^3 + a * (1 - 2 * Complex.I)^2 - (1 - 2 * Complex.I) + b = 0) :
    a = 1 ∧ b = 15 := by
  rw [pow_three, pow_two] at h
  norm_num [Complex.ext_iff] at h
  constructor <;> linarith