import Mathlib

/- $a$, $b$ are positive numbers, and the parabolas $y=x^2+ax+2b$ and $y=x^2+2bx+a$ both intersect the $x$-axis. Then the minimum value of $a^2+b^2$ is ___          ___. -/
theorem algebra_220 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : ∃ x, x ^ 2 + a * x + 2 * b = 0) (h2 : ∃ x, x ^ 2 + 2 * b * x + a = 0) :
    a ^ 2 + b ^ 2 ≥ 20 := by

  rcases h1 with ⟨x1, hx1⟩
  have h1' : a ^ 2 - 8 * b ≥ 0 := by
    have h : (x1 + a / 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith [sq_nonneg (x1), sq_nonneg (x1 + a / 2), sq_nonneg (a), sq_nonneg (b)]

  rcases h2 with ⟨x2, hx2⟩
  have h2' : (2 * b) ^ 2 - 4 * a ≥ 0 := by
    have h : (x2 + b) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith [sq_nonneg (x2), sq_nonneg (x2 + b), sq_nonneg (a), sq_nonneg (b)]

  nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 2), 
          mul_pos ha hb,
          h1', h2']