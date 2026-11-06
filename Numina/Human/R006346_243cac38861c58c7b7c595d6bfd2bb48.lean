import Mathlib
/- Let $A$ be an integer and $M$ be a positive integer. An integer $n$ is sought that satisfies $0 \le n < M$ and $A \equiv n \pmod M$. Show that $n = A - M \cdot \lfloor A/M \rfloor$, where $\lfloor x \rfloor$ denotes the greatest integer less than or equal to $x$. -/
theorem number_theory_636143 (a m : ℤ) (n : ℕ) (hm : m > 0) (hn : n < m) (h : a ≡ n [ZMOD m]) : n = a - m * (a / m):= by
  -- First, prove that n equals a mod m using the congruence relation
  have h1 : n = a % m:= by
    -- Rewrite using the congruence hypothesis h
    rw [h]
    -- Use the fact that if a ≡ n (mod m) and 0 ≤ n < m, then n = a mod m
    refine Eq.symm (Int.emod_eq_of_lt (by positivity) hn)
  -- Replace n with a % m in the goal
  rw [h1]
  -- It suffices to prove the division algorithm: a = m * (a / m) + a % m
  suffices a = m * (a / m) + a % m by linarith
  -- This is exactly the division algorithm for integers
  exact Eq.symm (Int.ediv_add_emod a m)
