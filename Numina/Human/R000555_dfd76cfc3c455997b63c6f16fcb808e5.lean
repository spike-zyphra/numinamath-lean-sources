import Mathlib

/- Let $a$ and $b$ be real numbers.  One of the roots of $x^3 + ax + b = 0$ is $1 + i \sqrt{3}.$  Find $a + b.$ -/
theorem algebra_12370 (a b : ℝ) (h : (1 + Complex.I * Real.sqrt 3)^3 + a * (1 + Complex.I * Real.sqrt 3) + b = 0) :
    a + b = 8 := by
  simp [Complex.ext_iff, pow_three] at h
  ring_nf at h
  simp_all
  linarith