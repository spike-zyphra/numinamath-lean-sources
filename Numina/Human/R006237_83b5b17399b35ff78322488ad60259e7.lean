import Mathlib
/- Let $N$ be a positive integer and $k$ be an integer such that $k \ge 3$.
Let $A = N(10^k+1) + 10^{k-2} + 10^{k-3}$. Let $B = 10^k+1$.
Determine the integer quotient of $A$ by $B$. Show that the quotient is $N$. -/
theorem algebra_635057 (N k A B : ℕ) (hk : k ≥ 3) (hN : N > 0) (hA : A = N * (10 ^ k + 1) + 10 ^ (k - 2) + 10 ^ (k - 3)) (hB : B = 10 ^ k + 1) : A / B = N:= by
  -- Use division characterization: A/B = N iff N*B ≤ A < (N+1)*B
  refine Nat.div_eq_of_lt_le ?_ ?_
  .
    -- First goal: prove N*B ≤ A (lower bound)
    subst A B
    -- It suffices to show the remainder terms are non-negative
    suffices 10 ^ (k - 2) + 10 ^ (k - 3) ≥ 0 by linarith
    -- Powers of 10 are always positive
    positivity
  .
    -- Second goal: prove A < (N+1)*B (upper bound)
    subst A B
    -- It suffices to show the remainder is less than B
    suffices 10 ^ (k - 2) + 10 ^ (k - 3) < 10 ^ k + 1 by linarith
    -- Substitute m = k-3 to simplify the expressions
    set m:= k - 3 with hm
    clear_value m
    -- Express k in terms of m
    replace hm : k = m + 3:= by omega
    subst k
    -- Simplify the exponent: (m+3)-2 = m+1
    rw [show m + 3 - 2 = m + 1 by omega]
    -- Expand and simplify the inequality
    ring_nf
    -- Use the fact that 10^m is non-negative
    have g1 : 10 ^ m ≥ 0:= by positivity
    -- Complete the proof using linear arithmetic
    linarith
