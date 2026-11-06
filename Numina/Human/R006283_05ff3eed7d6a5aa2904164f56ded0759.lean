import Mathlib

/- Let $x$ and $d$ be positive integers such that $x > d$. Show that the sum of the cubes of the three integers $x-d$, $x$, and $x+d$, which is $(x-d)^3 + x^3 + (x+d)^3$, is composite. -/
theorem number_theory_635499 (x d : ℕ) (hx : 0 < x) (hd : 0 < d) (h : x > d) : ∃ m n, 1 < m ∧ 1 < n ∧ m * n = (x - d) ^ 3 + x ^ 3 + (x + d) ^ 3 := by
  -- We expand the expression
  -- (x - d) ^ 3 + x ^ 3 + (x + d) ^ 3 = 3 * x * (x ^ 2 + 2 * d ^ 2)
  -- So we can take m = 3 and n = x * (x ^ 2 + 2 * d ^ 2)
  use 3, x * (x ^ 2 + 2 * d ^ 2)
  simp
  constructor
  . -- It is greater than 1 clearly
    nlinarith
  . -- Cast to ℤ
    zify [h.lt]
    -- It's a ring identity
    ring
