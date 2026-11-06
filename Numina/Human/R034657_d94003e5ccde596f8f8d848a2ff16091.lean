import Mathlib


/-- Given the sequence $\left\{a_{n}\right\}$ satisfies:
    $a_{1}=2, a_{n}=2\left(n+a_{n-1}\right), n=2,3, \cdots$,
    find the general term formula of the sequence $\left\{a_{n}\right\}$. -/
theorem algebra_127245 {a : ℕ → ℤ} (ha1 : a 1 = 2)
    (han : ∀ n ≥ 2, a n = 2 * (n + a (n - 1))) :
    ∀ n ≥ 1, a n = 2 ^ (n + 2) - 2 * n - 4 := by
  -- The sequence equals $2^{n+2} - 2n - 4$, which we show via induction.
  intro n ge
  induction n, ge using Nat.le_induction with
  -- The base case follows from $2^3 - 2 - 4 = 2$.
  | base => simp[ha1]
  | succ n hmn ind => 
    -- For the induction step, we need to show 
    -- $a_{n+1} = 2^{n+3} - 2(n+1) - 4$.
    -- Rewrite to $2n+2 + 2a_n = 2^{n+3} - 2(n+1) - 4$,
    rw[han (n + 1) (by simp[hmn])]
    norm_num
    rw[mul_add, mul_add]
    -- hence $2n+2 + 2 (2^{n+2} - 2n - 4) = 2^{n+3} - 2(n+1) - 4 = 2^{n+3} - 2n - 6$.
    rw[ind]
    -- But the LHS simplifies to $2n+2 + 2^{n+3} - 4n - 8$, as needed.
    ring