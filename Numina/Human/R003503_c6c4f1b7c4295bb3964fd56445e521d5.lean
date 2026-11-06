import Mathlib

/- 4. If $a_{0}=b_{0}=1, a_{n}=a_{n-1}+2 b_{n-1}, b_{n}=a_{n-1}+b_{n-1}(n=1,2, \cdots)$, then $a_{1993}^{2}-2 b_{1993}^{2}=(\quad)$. -/

theorem algebra_188966 {a b : ℕ → ℤ} (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (han : ∀ n, a (n + 1) = a n + 2 * b n) (hbn : ∀ n, b (n + 1) = a n + b n) :
    a 1993 ^ 2 - 2 * b 1993 ^ 2 = 1 := by

  -- We prove by induction on n that a n ^ 2 - 2 * b n ^ 2 = (-1) ^ (n + 1)
  have (n : ℕ) : a n ^ 2 - 2 * b n ^ 2 = (-1) ^(n + 1) := by
    induction' n with n hn
    · -- For n = 0 it is trivial
      rw [ha0, hb0]
      ring
    · -- For n + 1, we use the recurrence relations, and then it is an elementary identity
      rw [han, hbn, pow_succ (-1), ← hn]
      ring

  -- We conclude by evaluating the expression at n = 1993
  rw [this 1993, Even.neg_one_pow]
  use 997