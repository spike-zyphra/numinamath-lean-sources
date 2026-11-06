import Mathlib
/- Let $N$ be a positive integer. Consider the sum $S_N = \sum_{i=0}^{N-1} \frac{10^{i+1}-1}{9}$. Show that $S_N = \frac{10^{N+1} - 9N - 10}{81}$. -/
theorem algebra_638646 (n : ℕ) (hn : n > 0) : ∑ i in Finset.range n, (((10 : ℝ) ^ (i + 1) - 1) / 9) = (10 ^ (n + 1) - 9 * n - 10) / 81:= by
  -- Auxiliary lemma: prove the formula for sum up to n+1 terms using induction
  have h1 : ∀ n : ℕ, ∑ i in Finset.range (n + 1), (((10 : ℝ) ^ (i + 1) - 1) / 9) = (10 ^ (n + 2) - 9 * (n + 1) - 10) / 81:= by
    intro n
    -- Prove by induction on n
    induction n with
    | zero =>
      -- Base case: n = 0
      simp
      norm_num
    | succ n ih =>
      -- Inductive step: assume true for n, prove for n+1
      simp
      rw [Finset.sum_range_succ, ih]
      ring_nf
  -- Apply the auxiliary lemma with n-1
  specialize h1 (n - 1)
  -- Show that (n-1)+1 = n
  have g1 : n - 1 + 1 = n:= by omega
  rw [g1] at h1
  -- Convert natural number arithmetic to real number arithmetic
  rify at g1
  -- Express (n-1) as n-1 in real numbers
  replace g1 : (↑(n - 1) : ℝ) = (↑n : ℝ) - 1:= by linarith
  rw [g1] at h1
  -- Apply the rewritten auxiliary result
  rw [h1]
  -- Simplify the exponent: (n-1)+2 = n+1
  rw [show n - 1 + 2 = n + 1 by omega]
  -- Final algebraic simplification
  ring_nf
