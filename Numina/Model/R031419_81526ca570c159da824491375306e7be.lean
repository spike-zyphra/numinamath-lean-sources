import Mathlib

/- Let $a$ and $b$ be real numbers, and the function $f\left( x \right)=a{{x}^{2}}+b\left( x+1 \right)-2$. If for any real number $b$, the equation $a{{x}^{2}}+b\left( x+1 \right)-2=x$ has two distinct real roots, then the range of the real number $a$ is ___        ___. -/
theorem algebra_3572 (a : ℝ) (ha : ∀ b, ∃ x y, x ≠ y ∧ a * x ^ 2 + b * (x + 1) - 2 = x ∧ a * y ^ 2 + b * (y + 1) - 2 = y) :
    0 < a ∧ a < 1 := by

  have h1 := ha (1)
  rcases h1 with ⟨x, y, hxy, hx1, hy1⟩
  have eq1 : a * x ^ 2 - 1 = 0 := by linarith
  have eq2 : a * y ^ 2 - 1 = 0 := by linarith

  have h2 : a > 0 := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by
      intro h'
      apply hxy
      linarith
    ), sq_nonneg (x - y)]

  have h3 : a < 1 := by
    have h4 := ha (1 + 2 * a)
    rcases h4 with ⟨x, y, hxy, hx4, hy4⟩
    have h5 : a * x ^ 2 + 2 * a * x + (2 * a - 1) = 0 := by nlinarith
    have h6 : a * y ^ 2 + 2 * a * y + (2 * a - 1) = 0 := by nlinarith
    have h7 : a * (x ^ 2 - y ^ 2) + 2 * a * (x - y) = 0 := by nlinarith
    have h8 : (x - y) * (a * (x + y) + 2 * a) = 0 := by nlinarith
    have h9 : a * (x + y) + 2 * a = 0 := by
      apply (mul_left_inj' (show x - y ≠ 0 by
        intro h'
        apply hxy
        linarith
      )).mp
      linarith

    have h10 : (2 * a) ^ 2 - 4 * a * (2 * a - 1) > 0 := by
      nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by
        intro h'
        apply hxy
        linarith
      ), sq_nonneg (x - y), sq_nonneg (x + y + 2), h9]

    nlinarith

  constructor
  · exact h2
  · exact h3