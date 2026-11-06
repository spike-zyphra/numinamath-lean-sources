import Mathlib
/- Let $N$ be a positive integer. Compute the sum $\sum_{j=1}^{N} 2^j$. Show that the sum is equal to $2^{N+1}-2$. -/
theorem number_theory_637079 (N : ℕ) (hN : N > 0) : ∑ i in Finset.range N, 2 ^ (i + 1) = 2 ^ (N + 1) - 2:= by
  -- Helper lemma: Proves that for any natural number n, 2 + sum(2^(i+1)) from i=0 to n-1 equals 2^(n+1)
  have h1 : ∀ n : ℕ, 2 + ∑ i in Finset.range n, 2 ^ (i + 1) = 2 ^ (n + 1):= by
    intro n
    -- Proof by induction on n
    induction n with
    -- Base case: when n = 0
    | zero =>
      simp
    -- Inductive step: prove for n + 1 assuming it holds for n
    | succ n ih =>
      rw [Finset.sum_range_succ]
      -- Key step: shows that doubling 2^(n+1) equals 2^(n+2)
      suffices 2 ^ (n + 1) + 2 ^ (n + 1) = 2 ^ (n + 1 + 1) by linarith
      ring
  -- Apply the helper lemma with N and complete the proof using omega tactic
  specialize h1 N
  omega
