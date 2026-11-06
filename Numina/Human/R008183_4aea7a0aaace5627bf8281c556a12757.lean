import Mathlib

/- Let $x$ be a positive integer, and define the integers $n=x^2+2x+17$ and $d=2x+5$. When dividing $n$ by $d$, the quotient is $x$, and the remainder is $7$. Find $x$. -/
theorem algebra_10569 {x : ℤ} (hx : x > 0) (n d : ℤ)
    (hn : n = x ^ 2 + 2 * x + 17) (hd : d = 2 * x + 5)
    (hdiv : n / d = x ∧ n % d = 7) : x = 2 := by
  -- $n = d * (n / d) + n % d = d * x + 7$
  have h : n = d * x + 7 := by
    rw [← hdiv.1, ← hdiv.2]
    symm
    exact Int.ediv_add_emod _ _
  -- Substitute $n$ and $d$
  subst hn hd
  -- Solve the equation using nlinarith
  nlinarith
